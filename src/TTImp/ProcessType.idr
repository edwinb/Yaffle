module TTImp.ProcessType

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.Hash
import Core.Metadata
import Core.Evaluate
import Core.TT
import Core.Unify.State

import TTImp.Elab.Check
import TTImp.Elab.Utils
import TTImp.Elab
import TTImp.TTImp

import Data.List
import Data.List1
import Data.String
import Libraries.Data.NameMap
import Libraries.Data.StringMap

%default covering

getRetTy : {auto c : Ref Ctxt Defs} ->
           NF [<] -> Core Name
getRetTy (VBind fc _ (Pi _ _ _ _) sc)
    = getRetTy !(expand !(sc (pure (VErased fc Placeholder))))
getRetTy (VTCon _ n _ _) = pure n
getRetTy ty
    = throw (GenericMsg (getLoc ty)
             "Can only add hints for concrete return types")

throwIfHasFlag : {auto c : Ref Ctxt Defs} -> FC -> Name -> DefFlag -> String -> Core ()
throwIfHasFlag fc ndef fl msg
    = when !(hasFlag fc ndef fl) $ throw (GenericMsg fc msg)

processFnOpt : {auto c : Ref Ctxt Defs} ->
               FC -> Bool -> -- ^ top level name?
               Name -> FnOpt -> Core ()
processFnOpt fc _ ndef Inline
    = do throwIfHasFlag fc ndef NoInline "%noinline and %inline are mutually exclusive"
         setFlag fc ndef Inline
processFnOpt fc _ ndef NoInline
    = do throwIfHasFlag fc ndef Inline "%inline and %noinline are mutually exclusive"
         setFlag fc ndef NoInline
processFnOpt fc _ ndef Deprecate
    =  setFlag fc ndef Deprecate
processFnOpt fc _ ndef TCInline
    = setFlag fc ndef TCInline
processFnOpt fc True ndef (Hint d)
    = do defs <- get Ctxt
         Just ty <- lookupTyExact ndef (gamma defs)
              | Nothing => undefinedName fc ndef
         target <- getRetTy !(expand !(nf [<] ty))
         addHintFor fc target ndef d False
processFnOpt fc _ ndef (Hint d)
    = do log "elab" 5 $ "Adding local hint " ++ show !(toFullNames ndef)
         addLocalHint ndef
processFnOpt fc True ndef (GlobalHint a)
    = addGlobalHint ndef a
processFnOpt fc _ ndef (GlobalHint a)
    = throw (GenericMsg fc "%globalhint is not valid in local definitions")
processFnOpt fc _ ndef ExternFn
    = setFlag fc ndef Inline -- if externally defined, inline when compiling
processFnOpt fc _ ndef (ForeignFn _)
    = setFlag fc ndef Inline -- if externally defined, inline when compiling
processFnOpt fc _ ndef (ForeignExport _)
    = pure ()
processFnOpt fc _ ndef Invertible
    = setFlag fc ndef Invertible
processFnOpt fc _ ndef (Totality tot)
    = setFlag fc ndef (SetTotal tot)
processFnOpt fc _ ndef Macro
    = setFlag fc ndef Macro
processFnOpt fc _ ndef (SpecArgs ns)
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact ndef (gamma defs)
              | Nothing => undefinedName fc ndef
         nty <- expand !(nf [<] (type gdef))
         ps <- getNamePos 0 nty
         ddeps <- collectDDeps nty
         specs <- collectSpec [] ddeps ps nty
         ignore $ addDef ndef ({ specArgs := specs } gdef)
  where
    insertDeps : List Nat -> List (Name, Nat) -> List Name -> List Nat
    insertDeps acc ps [] = acc
    insertDeps acc ps (n :: ns)
        = case lookup n ps of
               Nothing => insertDeps acc ps ns
               Just pos => if pos `elem` acc
                              then insertDeps acc ps ns
                              else insertDeps (pos :: acc) ps ns

    -- Collect the argument names which the dynamic args depend on
    collectDDeps : NF [<] -> Core (List Name)
    collectDDeps (VBind tfc x (Pi _ _ _ nty) sc)
        = do defs <- get Ctxt
             sc' <- expand !(sc (pure (VApp tfc Bound x [<] (pure Nothing))))
             if x `elem` ns
                then collectDDeps sc'
                else do aty <- quote [<] nty
                        -- Get names depended on by nty
                        let deps = keys (getRefs (UN Underscore) aty)
                        rest <- collectDDeps sc'
                        pure (rest ++ deps)
    collectDDeps _ = pure []

    -- Return names the type depends on, and whether it's a parameter
    mutual
      getDepsArgs : Bool -> SnocList (NF [<]) -> NameMap Bool ->
                    Core (NameMap Bool)
      getDepsArgs inparam [<] ns = pure ns
      getDepsArgs inparam (as :< a) ns
          = do ns' <- getDeps inparam a ns
               getDepsArgs inparam as ns'

      getDeps : Bool -> NF [<] -> NameMap Bool ->
                Core (NameMap Bool)
      getDeps inparam (VLam _ x _ _ ty sc) ns
          = do defs <- get Ctxt
               ns' <- getDeps False !(expand ty) ns
               sc' <- expand !(sc (VErased fc Placeholder))
               getDeps False sc' ns
      getDeps inparam (VBind _ x (Pi _ _ _ pty) sc) ns
          = do defs <- get Ctxt
               ns' <- getDeps inparam !(expand pty) ns
               sc' <- expand !(sc (pure (VErased fc Placeholder)))
               getDeps inparam sc' ns'
      getDeps inparam (VBind _ x b sc) ns
          = do defs <- get Ctxt
               ns' <- getDeps False !(expand (binderType b)) ns
               sc' <- expand !(sc (pure (VErased fc Placeholder)))
               getDeps False sc' ns
      getDeps inparam (VApp _ Bound n args _) ns
          = do defs <- get Ctxt
               ns' <- getDepsArgs False !(traverseSnocList spineVal args) ns
               pure (insert n inparam ns')
      getDeps inparam (VDCon _ n t a args) ns
          = do defs <- get Ctxt
               getDepsArgs False !(traverseSnocList spineVal args) ns
      getDeps inparam (VTCon _ n a args) ns
          = do defs <- get Ctxt
               params <- case !(lookupDefExact n (gamma defs)) of
                              Just (TCon ti a) => pure (paramPos ti)
                              _ => pure []
               let (ps, ds) = splitPs 0 params
                                      (cast !(traverseSnocList spineVal args))
               ns' <- getDepsArgs True ps ns
               getDepsArgs False ds ns'
        where
          -- Split into arguments in parameter position, and others
          splitPs : Nat -> List Nat -> List (NF [<]) ->
                    (SnocList (NF [<]), SnocList (NF [<]))
          splitPs n params [] = ([<], [<])
          splitPs n params (x :: xs)
              = let (ps', ds') = splitPs (1 + n) params xs in
                    if n `elem` params
                       then (ps' :< x, ds')
                       else (ps', ds' :< x)
      getDeps inparam (VDelayed _ _ t) ns = getDeps inparam !(expand t) ns
      getDeps inparams nf ns = pure ns

    -- If the name of an argument is in the list of specialisable arguments,
    -- record the position. Also record the position of anything the argument
    -- depends on which is only dependend on by declared static arguments.
    collectSpec : List Nat -> -- specialisable so far
                  List Name -> -- things depended on by dynamic args
                               -- We're assuming  it's a short list, so just use
                               -- List and don't worry about duplicates.
                  List (Name, Nat) -> NF [<] -> Core (List Nat)
    collectSpec acc ddeps ps (VBind tfc x (Pi _ _ _ nty) sc)
        = do defs <- get Ctxt
             sc' <- expand !(sc (pure (VApp tfc Bound x [<] (pure Nothing))))
             if x `elem` ns
                then do deps <- getDeps True !(expand nty) NameMap.empty
                        -- Get names depended on by nty
                        -- Keep the ones which are either:
                        --  * parameters
                        --  * not depended on by a dynamic argument (the ddeps)
                        let rs = filter (\x => snd x ||
                                               not (fst x `elem` ddeps))
                                        (toList deps)
                        let acc' = insertDeps acc ps (x :: map fst rs)
                        collectSpec acc' ddeps ps sc'
                else collectSpec acc ddeps ps sc'
    collectSpec acc ddeps ps _ = pure acc

    getNamePos : Nat -> NF [<] -> Core (List (Name, Nat))
    getNamePos i (VBind tfc x (Pi _ _ _ _) sc)
        = do defs <- get Ctxt
             ns' <- getNamePos (1 + i) !(expand !(sc (pure (VErased tfc Placeholder))))
             pure ((x, i) :: ns')
    getNamePos _ _ = pure []

getFnString : {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto u : Ref UST UState} ->
               RawImp -> Core String
getFnString (IPrimVal _ (Str st)) = pure st
getFnString tm
    = do inidx <- resolveName (UN $ Basic "[foreign]")
         let fc = getFC tm
         gstr <- nf [<] (PrimVal fc $ PrT StringType)
         etm <- checkTerm inidx InExpr [] (MkNested []) [<] tm gstr
         defs <- get Ctxt
         case !(expand !(nf [<] etm)) of
              VPrimVal fc (Str st) => pure st
              _ => throw (GenericMsg fc "%foreign calling convention must evaluate to a String")

-- If it's declared as externally defined, set the definition to
-- ExternFn <arity>, where the arity is assumed to be fixed (i.e.
-- not dependent on any of the arguments)
-- Similarly set foreign definitions. Possibly combine these?
initDef : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          {auto m : Ref MD Metadata} ->
          {auto u : Ref UST UState} ->
          FC -> Name -> Env Term vars -> Term vars -> List FnOpt -> Core Def
initDef fc n env ty []
    = do addUserHole False n
         pure None
initDef fc n env ty (ExternFn :: opts)
    = do defs <- get Ctxt
         a <- getArity env ty
         pure (ExternDef a)
initDef fc n env ty (ForeignFn cs :: opts)
    = do defs <- get Ctxt
         a <- getArity env ty
         cs' <- traverse getFnString cs
         pure (ForeignDef a cs')
-- In this case, nothing to initialise to, but we do need to process the
-- calling conventions then process the rest of the options.
-- This means, for example, we can technically re-export something foreign!
-- I suppose that may be useful one day...
initDef fc n env ty (ForeignExport cs :: opts)
    = do cs' <- traverse getFnString cs
         conv <- traverse getConvention cs'
         defs <- get Ctxt
         put Ctxt ({ foreignExports $= insert n conv } defs)
         initDef fc n env ty opts
  where
    getConvention : String -> Core (String, String)
    getConvention c
        = do let (lang ::: fname :: []) = split (== ':') c
                 | _ => throw (GenericMsg fc "Invalid calling convention")
             pure (trim lang, trim fname)
initDef fc n env ty (_ :: opts) = initDef fc n env ty opts

-- Find the inferrable argument positions in a type. This is useful for
-- generalising partially evaluated definitions and (potentially) in interactive
-- editing
findInferrable : {auto c : Ref Ctxt Defs} ->
                 NF [<] -> Core (List Nat)
findInferrable ty = fi 0 0 [] [] ty
  where
    mutual
      -- Add to the inferrable arguments from the given type. An argument is
      -- inferrable if it's guarded by a constructor, or on its own
      findInf : List Nat -> List (Name, Nat) ->
                NF [<] -> Core (List Nat)
      findInf acc pos (VApp _ Bound n [<] _)
          = case lookup n pos of
                 Nothing => pure acc
                 Just p => if p `elem` acc then pure acc else pure (p :: acc)
      findInf acc pos (VDCon _ _ _ _ args)
          = do args' <- traverseSnocList spineVal args
               findInfs acc pos args'
      findInf acc pos (VTCon _ _ _ args)
          = do args' <- traverseSnocList spineVal args
               findInfs acc pos args'
      findInf acc pos (VDelayed _ _ t) = findInf acc pos !(expand t)
      findInf acc _ _ = pure acc

      findInfs : List Nat -> List (Name, Nat) -> SnocList (NF [<]) -> Core (List Nat)
      findInfs acc pos [<] = pure acc
      findInfs acc pos (ns :< n) = findInf !(findInfs acc pos ns) pos n

    fi : Nat -> Int -> List (Name, Nat) -> List Nat -> NF [<] -> Core (List Nat)
    fi pos i args acc (VBind fc x (Pi _ _ _ aty) sc)
        = do let argn = MN "inf" i
             sc' <- expand !(sc (pure (VApp fc Bound argn [<] (pure Nothing))))
             acc' <- findInf acc args !(expand aty)
             rest <- fi (1 + pos) (1 + i) ((argn, pos) :: args) acc' sc'
             pure rest
    fi pos i args acc ret = findInf acc args ret

checkForShadowing : (env : StringMap FC) -> RawImp -> List (String, FC, FC)
checkForShadowing env (IPi fc _ _ (Just (UN (Basic name))) argTy retTy) =
    let argShadowing = checkForShadowing empty argTy
     in (case lookup name env of
        Just origFc => (name, origFc, fc) :: checkForShadowing env retTy
        Nothing => checkForShadowing (insert name fc env) retTy)
        ++ argShadowing
checkForShadowing env t = []

export
processType : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto u : Ref UST UState} ->
              List ElabOpt -> NestedNames vars -> Env Term vars ->
              FC -> RigCount -> Visibility ->
              List FnOpt -> ImpTy -> Core ()
processType {vars} eopts nest env fc rig vis opts (MkImpTy tfc nameFC n_in ty_raw)
    = do n <- inCurrentNS n_in

         addNameLoc nameFC n

         log "declare.type" 1 $ "Processing " ++ show n
         log "declare.type" 5 $ unwords ["Checking type decl:", show rig, show n, ":", show ty_raw]
         idx <- resolveName n

         -- Check 'n' is undefined
         defs <- get Ctxt
         Nothing <- lookupCtxtExact (Resolved idx) (gamma defs)
              | Just gdef => throw (AlreadyDefined fc n)

         u <- uniVar fc
         ty <-
             wrapErrorC eopts (InType fc n) $
                   checkTerm idx InType (HolesOkay :: eopts) nest env
                             (IBindHere fc (PI erased) ty_raw)
                             (VType fc u)
         logTermNF "declare.type" 3 ("Type of " ++ show n) [<] (abstractFullEnvType tfc env ty)

         def <- initDef fc n env ty opts
         let fullty = abstractFullEnvType tfc env ty

         (erased, dterased) <- findErased fullty
         defs <- get Ctxt
         infargs <- findInferrable !(expand !(nf [<] fullty))

         ignore $ addDef (Resolved idx)
                ({ eraseArgs := erased,
                   safeErase := dterased,
                   inferrable := infargs }
                 (newDef fc n rig vars fullty vis def))

         log "declare.type" 2 $ "Setting options for " ++ show n ++ ": " ++ show opts
         let name = Resolved idx
         let isNested : Name -> Bool
             isNested (Nested _ _) = True
             isNested (NS _ n) = isNested n
             isNested _ = False
         let nested = not (isNested n)
         traverse_ (processFnOpt fc (not (isNested n)) name) opts
         -- If no function-specific totality pragma has been used, attach the default totality
         unless (any isTotalityReq opts) $
           setFlag fc name (SetTotal !getDefaultTotalityOption)

         -- Add to the interactive editing metadata
         addTyDecl fc (Resolved idx) env ty -- for definition generation

         log "metadata.names" 7 $ "processType is adding ↓"
         addNameType nameFC (Resolved idx) env ty -- for looking up types

         traverse_ addToSave (keys (getMetas ty))
         addToSave n
         log "declare.type" 10 $ "Saving from " ++ show n ++ ": " ++ show (keys (getMetas ty))

         when (vis /= Private) $
              do addHashWithNames n
                 addHashWithNames ty
                 log "module.hash" 15 "Adding hash for type with name \{show n}"
         when (showShadowingWarning !getSession) $
            whenJust (fromList (checkForShadowing StringMap.empty ty_raw))
                $ recordWarning . ShadowingLocalBindings fc
