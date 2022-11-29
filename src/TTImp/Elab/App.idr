module TTImp.Elab.App

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.Metadata
import Core.Evaluate
import Core.Evaluate.QuoteB
import Core.Unify
import Core.Unify.SolveMeta
import Core.TT

import TTImp.Elab.Check
import TTImp.Elab.Dot
import TTImp.TTImp

import Data.List
import Data.Maybe
import Data.SnocList

%default covering

checkVisibleNS : {auto c : Ref Ctxt Defs} ->
                 FC -> Name -> Visibility -> Core ()
checkVisibleNS fc (NS ns x) vis
    = if !(isVisible ns)
         then if !isAllPublic
                       || visibleInAny (!getNS :: !getNestedNS) (NS ns x) vis
                 then pure ()
                 else throw $ InvisibleName fc (NS ns x) Nothing
         else throw $ InvisibleName fc (NS ns x) (Just ns)
checkVisibleNS _ _ _ = pure ()

onLHS : ElabMode -> Bool
onLHS (InLHS _) = True
onLHS _ = False

-- Get the type of a variable, assuming we haven't found it in the nested
-- names. Look in the Env first, then the global context.
getNameType : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto e : Ref EST (EState vars)} ->
              ElabMode ->
              RigCount -> Env Term vars ->
              FC -> Name ->
              Core (Term vars, Glued vars)
getNameType elabMode rigc env fc x
    = case defined x env of
           Just (MkIsDefined rigb lv) =>
              do rigSafe rigb rigc
                 let binder = getBinder lv env
                 let bty = binderType binder

                 log "metadata.names" 7 $ "getNameType is adding ↓"
                 addNameType fc x env bty

                 when (isLinear rigb) $ update EST { linearUsed $= ((MkVar lv) :: ) }
                 log "ide-mode.highlight" 8
                     $ "getNameType is trying to add Bound: "
                      ++ show x ++ " (" ++ show fc ++ ")"
                 when (isSourceName x) $
                   whenJust (isConcreteFC fc) $ \nfc => do
                     log "ide-mode.highlight" 7 $ "getNameType is adding Bound: " ++ show x
                     addSemanticDecorations [(nfc, Bound, Just x)]

                 pure (Local fc (Just (isLet binder)) _ lv, !(nf env bty))
           Nothing =>
              do defs <- get Ctxt
                 [(pname, i, def)] <- lookupCtxtName x (gamma defs)
                      | ns => ambiguousName fc x (map fst ns)
                 checkVisibleNS fc (fullname def) (visibility def)
                 when (not $ onLHS elabMode) $
                   checkDeprecation fc def
                 rigSafe (multiplicity def) rigc
                 let nt = fromMaybe Func (defNameType $ definition def)

                 log "ide-mode.highlight" 8
                     $ "getNameType is trying to add something for: "
                      ++ show def.fullname ++ " (" ++ show fc ++ ")"

                 when (isSourceName def.fullname) $
                   whenJust (isConcreteFC fc) $ \nfc => do
                     let decor = nameDecoration def.fullname nt
                     log "ide-mode.highlight" 7
                       $ "getNameType is adding " ++ show decor ++ ": " ++ show def.fullname
                     addSemanticDecorations [(nfc, decor, Just def.fullname)]

                 pure (Ref fc nt (Resolved i), !(nf env (embed (type def))))
  where
    rigSafe : RigCount -> RigCount -> Core ()
    rigSafe lhs rhs = when (lhs < rhs)
                           (throw (LinearMisuse fc !(getFullName x) lhs rhs))

    checkDeprecation : FC -> GlobalDef -> Core ()
    checkDeprecation fc gdef =
      do when (Deprecate `elem` gdef.flags) $
           recordWarning $
             Deprecated
               "\{show gdef.fullname} is deprecated and will be removed in a future version."
               (Just (fc, gdef.fullname))

-- Get the type of a variable, looking it up in the nested names first.
getVarType : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto e : Ref EST (EState vars)} ->
             ElabMode ->
             RigCount -> NestedNames vars -> Env Term vars ->
             FC -> Name ->
             Core (Term vars, Nat, Glued vars)
getVarType elabMode rigc nest env fc x
    = case lookup x (names nest) of
           Nothing => do (tm, ty) <- getNameType elabMode rigc env fc x
                         pure (tm, 0, ty)
           Just (nestn, argns, tmf) =>
              do defs <- get Ctxt
                 let arglen = length argns
                 let n' = fromMaybe x nestn
                 case !(lookupCtxtExact n' (gamma defs)) of
                      Nothing => undefinedName fc n'
                      Just ndef =>
                         let nt = fromMaybe Func (defNameType $ definition ndef)
                             tm = tmf fc nt
                             tyenv = useVars (getArgs tm)
                                             (embed (type ndef)) in
                             do checkVisibleNS fc (fullname ndef) (visibility ndef)
                                logTerm "elab" 5 ("Type of " ++ show n') tyenv
                                logTerm "elab" 5 ("Expands to") tm
                                log "elab" 5 $ "Arg length " ++ show arglen

                                -- Add the type to the metadata
                                log "metadata.names" 7 $ "getVarType is adding ↓"
                                addNameType fc x env tyenv

                                when (isSourceName ndef.fullname) $
                                  whenJust (isConcreteFC fc) $ \nfc => do
                                    let decor = nameDecoration ndef.fullname nt
                                    log "ide-mode.highlight" 7
                                       $ "getNameType is adding "++ show decor ++": "
                                                                 ++ show ndef.fullname
                                    addSemanticDecorations [(nfc, decor, Just ndef.fullname)]

                                pure (tm, arglen, !(nf env tyenv))
    where
      useVars : {vars : _} ->
                List (Term vars) -> Term vars -> Term vars
      useVars [] sc = sc
      useVars (a :: as) (Bind bfc n (Pi fc c _ ty) sc)
           = Bind bfc n (Let fc c a ty) (useVars (map weaken as) sc)
      useVars as (Bind bfc n (Let fc c v ty) sc)
           = Bind bfc n (Let fc c v ty) (useVars (map weaken as) sc)
      useVars _ sc = sc -- Can't happen?

isHole : NF vars -> Bool
isHole (VMeta{}) = True
isHole _ = False

-- Check an application of 'fntm', with type 'fnty' to the given list
-- of explicit and implicit arguments.
-- Returns the checked term and its (weakly) normalised type
checkAppWith' : {vars : _} ->
                {auto c : Ref Ctxt Defs} ->
                {auto m : Ref MD Metadata} ->
                {auto u : Ref UST UState} ->
                {auto e : Ref EST (EState vars)} ->
                RigCount -> ElabInfo ->
                NestedNames vars -> Env Term vars ->
                FC -> (fntm : Term vars) -> (fnty : NF vars) ->
                (argdata : (Maybe Name, Nat)) ->
                     -- function we're applying, and argument position, for
                     -- checking if it's okay to erase against 'safeErase'
                (expargs : List RawImp) ->
                (autoargs : List RawImp) ->
                (namedargs : List (Name, RawImp)) ->
                (knownret : Bool) -> -- Do we know what the return type is yet?
                             -- if we do, we might be able to use it to work
                             -- out the types of arguments before elaborating them
                (expected : Maybe (Glued vars)) ->
                Core (Term vars, Glued vars)

||| Entrypoint for checkAppWith: run the elaboration first and, if we're
||| on the LHS and the result is an under-applied constructor then insist
||| that it ought to be forced by another pattern somewhere else in the LHS.
checkAppWith : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               {auto m : Ref MD Metadata} ->
               {auto u : Ref UST UState} ->
               {auto e : Ref EST (EState vars)} ->
               RigCount -> ElabInfo ->
               NestedNames vars -> Env Term vars ->
               FC -> (fntm : Term vars) -> (fnty : NF vars) ->
               (argdata : (Maybe Name, Nat)) ->
                    -- function we're applying, and argument position, for
                    -- checking if it's okay to erase against 'safeErase'
               (expargs : List RawImp) ->
               (autoargs : List RawImp) ->
               (namedargs : List (Name, RawImp)) ->
               (knownret : Bool) -> -- Do we know what the return type is yet?
                            -- if we do, we might be able to use it to work
                            -- out the types of arguments before elaborating them
               (expected : Maybe (Glued vars)) ->
               Core (Term vars, Glued vars)
checkAppWith rig info nest env fc tm ty
  argdata expargs autoargs namedargs knownret expected
  = do res <- checkAppWith' rig info nest env fc tm ty
                 argdata expargs autoargs namedargs knownret expected
       let Just _ = isLHS (elabMode info)
             | Nothing => pure res
       let (Ref _ t _, args) = getFnArgs (fst res)
             | _ => pure res
       let Just (_, a) = isCon t
             | _ => pure res
       if a == length args
         then pure res
         else registerDot rig env fc UnderAppliedCon (fst res) (snd res)


makeImplicit : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               {auto m : Ref MD Metadata} ->
               {auto u : Ref UST UState} ->
               {auto e : Ref EST (EState vars)} ->
               RigCount -> RigCount -> ElabInfo ->
               NestedNames vars -> Env Term vars ->
               FC -> (fntm : Term vars) -> RigCount ->
               Name -> Glued vars -> (Glued vars -> Core (Glued vars)) ->
               (argdata : (Maybe Name, Nat)) ->
               (expargs : List RawImp) ->
               (autoargs : List RawImp) ->
               (namedargs : List (Name, RawImp)) ->
               (knownret : Bool) ->
               (expected : Maybe (Glued vars)) ->
               Core (Term vars, Glued vars)
makeImplicit rig argRig elabinfo nest env fc tm tmrig x aty sc (n, argpos) expargs autoargs namedargs kr expty
    = do nm <- genMVName x
         metaty <- quote env aty
         metaval <- metaVar fc argRig env nm metaty
         let fntm = App fc tm tmrig metaval
         fnty <- expand !(sc !(nf env metaval))
         when (bindingVars elabinfo) $ update EST $ addBindIfUnsolved nm argRig Implicit env metaval metaty
         checkAppWith rig elabinfo nest env fc
                      fntm fnty (n, 1 + argpos) expargs autoargs namedargs kr expty

makeAutoImplicit : {vars : _} ->
                   {auto c : Ref Ctxt Defs} ->
                   {auto m : Ref MD Metadata} ->
                   {auto u : Ref UST UState} ->
                   {auto e : Ref EST (EState vars)} ->
                   RigCount -> RigCount -> ElabInfo ->
                   NestedNames vars -> Env Term vars ->
                   FC -> (fntm : Term vars) -> RigCount ->
                   Name -> Glued vars -> (Glued vars -> Core (Glued vars)) ->
                   (argpos : (Maybe Name, Nat)) ->
                   (expargs : List RawImp) ->
                   (autoargs : List RawImp) ->
                   (namedargs : List (Name, RawImp)) ->
                   (knownret : Bool) ->
                   (expected : Maybe (Glued vars)) ->
                   Core (Term vars, Glued vars)
makeAutoImplicit rig argRig elabinfo nest env fc tm tmrig x aty sc (n, argpos) expargs autoargs namedargs kr expty
-- on the LHS, just treat it as an implicit pattern variable.
-- on the RHS, add a searchable hole
    = if metavarImp (elabMode elabinfo)
         then do nm <- genMVName x
                 metaty <- quote env aty
                 metaval <- metaVar fc argRig env nm metaty
                 let fntm = App fc tm tmrig metaval
                 fnty <- expand !(sc !(nf env metaval))
                 update EST $ addBindIfUnsolved nm argRig AutoImplicit env metaval metaty
                 checkAppWith rig elabinfo nest env fc
                              fntm fnty (n, 1 + argpos) expargs autoargs namedargs kr expty
         else do nm <- genMVName x
                 metaty <- quote env aty
                 est <- get EST
                 lim <- getAutoImplicitLimit
                 metaval <- searchVar fc argRig lim (Resolved (defining est))
                                      env nest nm metaty
                 let fntm = App fc tm tmrig metaval
                 fnty <- expand !(sc !(nf env metaval))
                 checkAppWith rig elabinfo nest env fc
                              fntm fnty (n, 1 + argpos) expargs autoargs namedargs kr expty
  where
    metavarImp : ElabMode -> Bool
    metavarImp (InLHS _) = True
    metavarImp InTransform = True
    metavarImp _ = False

makeDefImplicit : {vars : _} ->
                  {auto c : Ref Ctxt Defs} ->
                  {auto m : Ref MD Metadata} ->
                  {auto u : Ref UST UState} ->
                  {auto e : Ref EST (EState vars)} ->
                  RigCount -> RigCount -> ElabInfo ->
                  NestedNames vars -> Env Term vars ->
                  FC -> (fntm : Term vars) -> RigCount ->
                  Name -> Glued vars -> Glued vars -> (Glued vars -> Core (Glued vars)) ->
                  (argpos : (Maybe Name, Nat)) ->
                  (expargs : List RawImp) ->
                  (autoargs : List RawImp) ->
                  (namedargs : List (Name, RawImp)) ->
                  (knownret : Bool) ->
                  (expected : Maybe (Glued vars)) ->
                  Core (Term vars, Glued vars)
makeDefImplicit rig argRig elabinfo nest env fc tm tmrig x arg aty sc (n, argpos) expargs autoargs namedargs kr expty
-- on the LHS, just treat it as an implicit pattern variable.
-- on the RHS, use the default
    = if metavarImp (elabMode elabinfo)
         then do nm <- genMVName x
                 metaty <- quote env aty
                 metaval <- metaVar fc argRig env nm metaty
                 let fntm = App fc tm tmrig metaval
                 fnty <- expand !(sc !(nf env metaval))
                 update EST $ addBindIfUnsolved nm argRig AutoImplicit env metaval metaty
                 checkAppWith rig elabinfo nest env fc
                              fntm fnty (n, 1 + argpos) expargs autoargs namedargs kr expty
         else do aval <- quote env arg
                 let fntm = App fc tm tmrig aval
                 fnty <- expand !(sc arg)
                 checkAppWith rig elabinfo nest env fc
                              fntm fnty (n, 1 + argpos) expargs autoargs namedargs kr expty
  where
    metavarImp : ElabMode -> Bool
    metavarImp (InLHS _) = True
    metavarImp InTransform = True
    metavarImp _ = False

-- Defer elaborating anything which will be easier given a known target
-- type (ambiguity, cases, etc)
needsDelayExpr : {auto c : Ref Ctxt Defs} ->
                 (knownRet : Bool) -> RawImp ->
                 Core Bool
needsDelayExpr False _ = pure False
needsDelayExpr True (IVar fc n)
    = do defs <- get Ctxt
         pure $ case !(lookupCtxtName n (gamma defs)) of
                     (_ :: _ :: _) => True
                     _ => False
needsDelayExpr True (IApp _ f _) = needsDelayExpr True f
needsDelayExpr True (IAutoApp _ f _) = needsDelayExpr True f
needsDelayExpr True (INamedApp _ f _ _) = needsDelayExpr True f
needsDelayExpr True (ILam _ _ _ _ _ _) = pure True
needsDelayExpr True (ICase _ _ _ _) = pure True
needsDelayExpr True (ILocal _ _ _) = pure True
needsDelayExpr True (IUpdate _ _ _) = pure True
needsDelayExpr True (IAlternative _ _ _) = pure True
needsDelayExpr True (ISearch _ _) = pure True
needsDelayExpr True (IRewrite _ _ _) = pure True
needsDelayExpr True _ = pure False

-- On the LHS, for any concrete thing, we need to make sure we know
-- its type before we proceed so that we can reject it if the type turns
-- out to be polymorphic
needsDelayLHS : {auto c : Ref Ctxt Defs} ->
                RawImp -> Core Bool
needsDelayLHS (IVar fc n) = pure True
needsDelayLHS (IApp _ f _) = needsDelayLHS f
needsDelayLHS (IAutoApp _ f _) = needsDelayLHS f
needsDelayLHS (INamedApp _ f _ _) = needsDelayLHS f
needsDelayLHS (IAlternative _ _ _) = pure True
needsDelayLHS (IAs _ _ _ _ t) = needsDelayLHS t
needsDelayLHS (ISearch _ _) = pure True
needsDelayLHS (IPrimVal _ _) = pure True
needsDelayLHS (IType _) = pure True
needsDelayLHS (IWithUnambigNames _ _ t) = needsDelayLHS t
needsDelayLHS _ = pure False

needsDelay : {auto c : Ref Ctxt Defs} ->
             ElabMode ->
             (knownRet : Bool) -> RawImp ->
             Core Bool
needsDelay (InLHS _) _ tm = needsDelayLHS tm
needsDelay _ kr tm = needsDelayExpr kr tm

checkValidPattern :
  {vars : _} ->
  {auto c : Ref Ctxt Defs} ->
  {auto m : Ref MD Metadata} ->
  {auto u : Ref UST UState} ->
  {auto e : Ref EST (EState vars)} ->
  RigCount -> Env Term vars -> FC ->
  Term vars -> Glued vars ->
  Core (Term vars, Glued vars)
checkValidPattern rig env fc tm ty
  = do log "elab.app.lhs" 50 $ "Checking that " ++ show tm ++ " is a valid pattern"
       case tm of
         Bind _ _ (Lam _ _ _ _)  _ => registerDot rig env fc NotConstructor tm ty
         _ => pure (tm, ty)

dotErased : {vars : _} ->
            {auto c : Ref Ctxt Defs} -> (argty : Glued vars) ->
            Maybe Name -> Nat -> ElabMode -> RigCount -> RawImp -> Core RawImp
dotErased argty mn argpos (InLHS lrig ) rig tm
    = if not (isErased lrig) && isErased rig
        then do
          -- if the argument type aty has a single constructor, there's no need
          -- to dot it
          defs <- get Ctxt
          nfargty <- expand argty
          mconsCount <- countConstructors nfargty
          logNF "elab.app.dot" 50
            "Found \{show mconsCount} constructors for type"
            (mkEnv emptyFC vars)
            nfargty
          if mconsCount == Just 1 || mconsCount == Just 0
            then pure tm
            else
              -- if argpos is an erased position of 'n', leave it, otherwise dot if
              -- necessary
              do Just gdef <- maybe (pure Nothing) (\n => lookupCtxtExact n (gamma defs)) mn
                      | Nothing => pure (dotTerm tm)
                 if argpos `elem` safeErase gdef
                    then pure tm
                    else pure $ dotTerm tm
        else pure tm
  where
    -- TODO: this seems too conservative. If we get back an expression stuck on a
    -- meta, shouldn't we delay the check instead of declaring the tm dotted?
    ||| Count the constructors of a fully applied concrete datatype
    countConstructors : NF vars -> Core (Maybe Nat)
    countConstructors (VTCon _ tycName n args) =
      if length args == n
      then do defs <- get Ctxt
              Just gdef <- lookupCtxtExact tycName (gamma defs)
                  | Nothing => pure Nothing
              let (TCon ti ar) = gdef.definition
                  | _ => pure Nothing
              pure (Just (length (datacons ti)))
      else pure Nothing
    countConstructors _ = pure Nothing

    dotTerm : RawImp -> RawImp
    dotTerm tm
        = case tm of
               IMustUnify _ _ _ => tm
               IBindVar _ _ => tm
               Implicit _ _ => tm
               IAs _ _ _ _ (IBindVar _ _) => tm
               IAs _ _ _ _ (Implicit _ _) => tm
               IAs fc nameFC p t arg => IAs fc nameFC p t (IMustUnify fc ErasedArg tm)
               _ => IMustUnify (getFC tm) ErasedArg tm
dotErased _ _ _ _ _ tm = pure tm

-- Check the rest of an application given the argument type and the
-- raw argument. We choose elaboration order depending on whether we know
-- the return type now. If we know it, elaborate the rest of the
-- application first and come back to it, because that might infer types
-- for implicit arguments, which might in turn help with type-directed
-- disambiguation when elaborating the argument.
checkRestApp : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               {auto m : Ref MD Metadata} ->
               {auto u : Ref UST UState} ->
               {auto e : Ref EST (EState vars)} ->
               RigCount -> RigCount -> ElabInfo ->
               NestedNames vars -> Env Term vars ->
               FC -> (fntm : Term vars) -> Name ->
               RigCount -> (aty : Glued vars) -> (sc : Glued vars -> Core (Glued vars)) ->
               (argdata : (Maybe Name, Nat)) ->
               (arg : RawImp) ->
               (expargs : List RawImp) ->
               (autoargs : List RawImp) ->
               (namedargs : List (Name, RawImp)) ->
               (knownret : Bool) ->
               (expected : Maybe (Glued vars)) ->
               Core (Term vars, Glued vars)
checkRestApp rig argRig elabinfo nest env fc tm x rigb aty sc
             (n, argpos) arg_in expargs autoargs namedargs knownret expty
   = do defs <- get Ctxt
        arg <- dotErased aty n argpos (elabMode elabinfo) argRig arg_in
        kr <- if knownret
                 then pure True
                 else do sc' <- sc (VErased fc Placeholder)
                         concrete env !(expand sc')
        -- In theory we can check the arguments in any order. But it turns
        -- out that it's sometimes better to do the rightmost arguments
        -- first to give ambiguity resolution more to work with. So
        -- we do that if the target type is unknown, or if we see that
        -- the raw term is otherwise worth delaying.
        if (isHole !(expand aty) && kr) || !(needsDelay (elabMode elabinfo) kr arg_in)
           then handle (checkRtoL kr arg)
                -- if the type isn't resolved, we might encounter an
                -- implicit that we can't use yet because we don't know
                -- about it. In that case, revert to LtoR
                  (\err => if invalidArg err
                              then checkLtoR kr arg
                              else throw err)
           else checkLtoR kr arg
  where
    invalidArg : Error -> Bool
    invalidArg (InvalidArgs{}) = True
    invalidArg _ = False

    checkRtoL : Bool -> -- return type is known
                RawImp -> -- argument currently being checked
                Core (Term vars, Glued vars)
    checkRtoL kr arg
      = do nm <- genMVName x
           metaty <- quote env aty
           (idx, metaval) <- argVar (getFC arg) argRig env nm metaty
           let fntm = App fc tm rigb metaval
           logTerm "elab" 10 "...as" metaval
           fnty <- expand !(sc !(nf env metaval))
           (tm, gty) <- checkAppWith rig elabinfo nest env fc
                                     fntm fnty (n, 1 + argpos) expargs autoargs namedargs kr expty
           aty' <- nf env metaty
           atyNF <- if onLHS (elabMode elabinfo)
                       then Just <$> expand aty'
                       else pure Nothing
           logNF "elab" 10 ("Now trying " ++ show nm ++ " " ++ show arg) env aty'

           -- On the LHS, checking an argument can't resolve its own type,
           -- it must be resolved from elsewhere. Otherwise we might match
           -- on things which are too specific for their polymorphic type.
           case atyNF of
                Just (VMeta _ _ i _ _ _) =>
                        do defs <- get Ctxt
                           Just gdef <- lookupCtxtExact (Resolved i) (gamma defs)
                                | Nothing => pure ()
                           when (isErased (multiplicity gdef)) $ addNoSolve i
                _ => pure ()
           res <- check argRig ({ topLevel := False } elabinfo) nest env arg (Just aty')
           case atyNF of
                Just (VMeta _ _ i _ _ _) => removeNoSolve i
                _ => pure ()

           (argv, argt) <-
             if not (onLHS (elabMode elabinfo))
               then pure res
               else do let (argv, argt) = res
                       checkValidPattern rig env fc argv argt

           -- If we're on the LHS, reinstantiate it with 'argv' because it
           -- *may* have as patterns in it and we need to retain them.
           -- (As patterns are a bit of a hack but I don't yet see a
           -- better way that leads to good code...)
           logTerm "elab" 10 ("Solving " ++ show metaval ++ " with") argv
           ok <- solveIfUndefined env metaval argv
           -- If there's a constraint, make a constant, but otherwise
           -- just return the term as expected
           tm <- if not ok
                    then do res <- convert fc elabinfo env
                                               !(nf env metaval)
                                               !(nf env argv)
                            let [] = constraints res
                                | cs => do tmty <- quote env gty
                                           newConstant fc rig env tm tmty cs
                            ignore $ updateSolution env metaval argv
                            pure tm
                    else pure tm
           when (onLHS $ elabMode elabinfo) $
               -- reset hole and redo it with the unexpanded definition
               do updateDef (Resolved idx) (const (Just (Hole 0 (holeInit False))))
                  ignore $ solveIfUndefined env metaval argv
           removeHole idx
           pure (tm, gty)

    checkLtoR : Bool -> -- return type is known
                RawImp -> -- argument currently being checked
                Core (Term vars, Glued vars)
    checkLtoR kr arg
      = do logNF "elab" 10 ("Full function type") env
                 (VBind {f=Normal} fc x (Pi fc rigb Explicit aty) sc)
           logC "elab" 10
                   (do ety <- maybe (pure Nothing)
                                   (\t => pure (Just !(toFullNames !(quote env t))))
                                   expty
                       pure ("Overall expected type: " ++ show ety))
           res <- check argRig ({ topLevel := False } elabinfo)
                                 nest env arg (Just aty)
           (argv, argt) <-
             if not (onLHS (elabMode elabinfo))
               then pure res
               else do let (argv, argt) = res
                       checkValidPattern rig env fc argv argt

           logNF "elab" 10 "Got arg type" env argt
           let fntm = App fc tm rigb argv
           fnty <- expand !(sc !(nf env argv))
           checkAppWith rig elabinfo nest env fc
                        fntm fnty (n, 1 + argpos) expargs autoargs namedargs kr expty

export
findNamed : Name -> List (Name, RawImp) -> Maybe ((Name, RawImp), List (Name, RawImp))
findNamed n l = case partition ((== n) . fst) l of
                     (x :: xs, ys) => Just (x, (xs ++ ys))
                     _ => Nothing

export
findBindAllExpPattern : List (Name, RawImp) -> Maybe RawImp
findBindAllExpPattern = lookup (UN Underscore)

isImplicitAs : RawImp -> Bool
isImplicitAs (IAs _ _ UseLeft _ (Implicit _ _)) = True
isImplicitAs _ = False

isBindAllExpPattern : Name -> Bool
isBindAllExpPattern (UN Underscore) = True
isBindAllExpPattern _ = False

 -- Explicit Pi, we use provided unnamed explicit argument
checkAppWith' rig elabinfo nest env fc tm ty@(VBind tfc x (Pi _ rigb Explicit aty) sc)
             argdata (arg :: expargs') autoargs namedargs kr expty
   = do let argRig = rig |*| rigb
        checkRestApp rig argRig elabinfo nest env fc
                     tm x rigb aty sc argdata arg expargs' autoargs namedargs kr expty
checkAppWith' rig elabinfo nest env fc tm ty@(VBind tfc x (Pi _ rigb Explicit aty) sc)
             argdata [] autoargs namedargs kr expty with (findNamed x namedargs)
 -- We found a compatible named argument
 checkAppWith' rig elabinfo nest env fc tm ty@(VBind tfc x (Pi _ rigb Explicit aty) sc)
              argdata [] autoargs namedargs kr expty | Just ((_, arg), namedargs')
  = do let argRig = rig |*| rigb
       checkRestApp rig argRig elabinfo nest env fc
                    tm x rigb aty sc argdata arg [] autoargs namedargs' kr expty
 checkAppWith' rig elabinfo nest env fc tm ty@(VBind tfc x (Pi _ rigb Explicit aty) sc)
              argdata [] autoargs namedargs kr expty | Nothing
  = case findBindAllExpPattern namedargs of
         Just arg => -- Bind-all-explicit pattern is present - implicitly bind
           do let argRig = rig |*| rigb
              checkRestApp rig argRig elabinfo nest env fc
                           tm x rigb aty sc argdata arg [] autoargs namedargs kr expty
         _ => if all isImplicitAs (autoargs
                                    ++ map snd (filter (not . isBindAllExpPattern . fst) namedargs))
                                                                  -- Only non-user implicit `as` bindings added by
                                                                  -- the compiler are allowed here
                 then -- We are done
                      checkExp rig elabinfo env fc tm (asGlued ty) expty
                 else -- Some user defined binding is present while we are out of explicit arguments, that's an error
                      throw (InvalidArgs fc env (map (const (UN $ Basic "<auto>")) autoargs ++ map fst namedargs) tm)
-- Function type is delayed, so force the term and continue
checkAppWith' rig elabinfo nest env fc tm (VDelayed dfc r ty) argdata expargs autoargs namedargs kr expty
    = checkAppWith' rig elabinfo nest env fc (TForce dfc r tm) !(expand ty)
                    argdata expargs autoargs namedargs kr expty
-- If there's no more arguments given, and the plicities of the type and
-- the expected type line up, stop
checkAppWith' rig elabinfo nest env fc tm ty@(VBind tfc x (Pi _ rigb Implicit aty) sc)
             argdata [] [] [] kr (Just expty_in)
    = do let argRig = rig |*| rigb
         expty <- expand expty_in
         case expty of
              VBind tfc' x' (Pi _ rigb' Implicit aty') sc'
                 => checkExp rig elabinfo env fc tm (asGlued ty) (Just expty_in)
              _ => makeImplicit rig argRig elabinfo nest env fc tm rigb x aty sc argdata [] [] [] kr (Just expty_in)
-- Same for auto
checkAppWith' rig elabinfo nest env fc tm ty@(VBind tfc x (Pi _ rigb AutoImplicit aty) sc)
             argdata [] [] [] kr (Just expty_in)
    = do let argRig = rig |*| rigb
         expty <- expand expty_in
         case expty of
              VBind tfc' x' (Pi _ rigb' AutoImplicit aty') sc'
                 => checkExp rig elabinfo env fc tm (asGlued ty) (Just expty_in)
              _ => makeAutoImplicit rig argRig elabinfo nest env fc tm rigb x aty sc argdata [] [] [] kr (Just expty_in)
-- Same for default
checkAppWith' rig elabinfo nest env fc tm ty@(VBind tfc x (Pi _ rigb (DefImplicit aval) aty) sc)
             argdata [] [] [] kr (Just expty_in)
    = do let argRig = rigMult rig rigb
         expty <- expand expty_in
         case expty of
              VBind tfc' x' (Pi _ rigb' (DefImplicit aval') aty') sc'
                 => if !(convert env aval aval')
                       then checkExp rig elabinfo env fc tm (asGlued ty) (Just expty_in)
                       else makeDefImplicit rig argRig elabinfo nest env fc tm rigb x aval aty sc argdata [] [] [] kr (Just expty_in)
              _ => makeDefImplicit rig argRig elabinfo nest env fc tm rigb x aval aty sc argdata [] [] [] kr (Just expty_in)

-- Check next unnamed auto implicit argument
checkAppWith' rig elabinfo nest env fc tm (VBind tfc x (Pi _ rigb AutoImplicit aty) sc)
             argdata expargs (arg :: autoargs') namedargs kr expty
    = checkRestApp rig (rig |*| rigb) elabinfo nest env fc
                       tm x rigb aty sc argdata arg expargs autoargs' namedargs kr expty
-- Check next named auto implicit argument
checkAppWith' rig elabinfo nest env fc tm (VBind tfc x (Pi _ rigb AutoImplicit aty) sc)
             argdata expargs [] namedargs kr expty
    = let argRig = rig |*| rigb in
          case findNamed x namedargs of
               Just ((_, arg), namedargs') =>
                  checkRestApp rig argRig elabinfo nest env fc
                               tm x rigb aty sc argdata arg expargs [] namedargs' kr expty
               Nothing =>
                       makeAutoImplicit rig argRig elabinfo nest env fc tm
                                            rigb x aty sc argdata expargs [] namedargs kr expty
-- Check next implicit argument
checkAppWith' rig elabinfo nest env fc tm (VBind tfc x (Pi _ rigb Implicit aty) sc)
             argdata expargs autoargs namedargs kr expty
    = let argRig = rig |*| rigb in
          case findNamed x namedargs of
             Nothing => makeImplicit rig argRig elabinfo nest env fc tm
                                     rigb x aty sc argdata expargs autoargs namedargs kr expty
             Just ((_, arg), namedargs') =>
                   checkRestApp rig argRig elabinfo nest env fc
                                tm x rigb aty sc argdata arg expargs autoargs namedargs' kr expty
-- Check next default argument
checkAppWith' rig elabinfo nest env fc tm (VBind tfc x (Pi _ rigb (DefImplicit arg) aty) sc)
             argdata expargs autoargs namedargs kr expty
    = let argRig = rigMult rig rigb in
          case findNamed x namedargs of
             Nothing => makeDefImplicit rig argRig elabinfo nest env fc tm
                                        rigb x arg aty sc argdata expargs autoargs namedargs kr expty
             Just ((_, arg), namedargs') =>
                   checkRestApp rig argRig elabinfo nest env fc
                                tm x rigb aty sc argdata arg expargs autoargs namedargs' kr expty
-- Invent a function type if we have extra explicit arguments but type is further unknown
checkAppWith' {vars} rig elabinfo nest env fc tm ty (n, argpos) (arg :: expargs) autoargs namedargs kr expty
    = -- Invent a function type,  and hope that we'll know enough to solve it
      -- later when we unify with expty
      do logNF "elab.with" 10 "Function type" env ty
         logTerm "elab.with" 10 "Function " tm
         argn <- genName "argTy"
         retn <- genName "retTy"
         u <- uniVar fc
         argTy <- metaVar fc erased env argn (TType fc u)
         argTyG <- nf env argTy
         retTy <- metaVar -- {vars = argn :: vars}
                          fc erased env -- (Pi RigW Explicit argTy :: env)
                          retn (TType fc u)
         (argv, argt) <- check rig elabinfo
                               nest env arg (Just argTyG)
         let fntm = App fc tm top argv
         fnty <- nf env retTy
         expfnty <- nf env (Bind fc argn (Pi fc top Explicit argTy) (weaken retTy))
         logNF "elab.with" 10 "Expected function type" env expfnty
         whenJust expty (logNF "elab.with" 10 "Expected result type" env)
         res <- checkAppWith' rig elabinfo nest env fc fntm !(expand fnty) (n, 1 + argpos) expargs autoargs namedargs kr expty
         cres <- Check.convert fc elabinfo env (asGlued ty) expfnty
         let [] = constraints cres
            | cs => do cty <- quote env expfnty
                       ctm <- newConstant fc rig env (fst res) cty cs
                       pure (ctm, !(nf env retTy))
         pure res
-- Only non-user implicit `as` bindings are allowed to be present as arguments at this stage
checkAppWith' rig elabinfo nest env fc tm ty argdata [] autoargs namedargs kr expty
    = if all isImplicitAs (autoargs ++ map snd (filter (not . isBindAllExpPattern . fst) namedargs))
         then checkExp rig elabinfo env fc tm (asGlued ty) expty
         else throw (InvalidArgs fc env (map (const (UN $ Basic "<auto>")) autoargs ++ map fst namedargs) tm)

export
checkApp : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto m : Ref MD Metadata} ->
           {auto u : Ref UST UState} ->
           {auto e : Ref EST (EState vars)} ->
           RigCount -> ElabInfo ->
           NestedNames vars -> Env Term vars ->
           FC -> (fn : RawImp) ->
           (expargs : List RawImp) ->
           (autoargs : List RawImp) ->
           (namedargs : List (Name, RawImp)) ->
           Maybe (Glued vars) ->
           Core (Term vars, Glued vars)
checkApp rig elabinfo nest env fc (IApp fc' fn arg) expargs autoargs namedargs exp
   = checkApp rig elabinfo nest env fc' fn (arg :: expargs) autoargs namedargs exp
checkApp rig elabinfo nest env fc (IAutoApp fc' fn arg) expargs autoargs namedargs exp
   = checkApp rig elabinfo nest env fc' fn expargs (arg :: autoargs) namedargs exp
checkApp rig elabinfo nest env fc (INamedApp fc' fn nm arg) expargs autoargs namedargs exp
   = checkApp rig elabinfo nest env fc' fn expargs autoargs ((nm, arg) :: namedargs) exp
checkApp rig elabinfo nest env fc (IVar fc' n) expargs autoargs namedargs exp
   = do (ntm, arglen, nty_in) <- getVarType elabinfo.elabMode rig nest env fc' n
        nty <- expand nty_in
        prims <- getPrimitiveNames
        elabinfo <- updateElabInfo prims elabinfo.elabMode n expargs elabinfo

        addNameLoc fc' n

        logC "elab" 10
                (do fnty <- quote env nty
                    exptyt <- maybe (pure Nothing)
                                       (\t => do ety <- quote env t
                                                 etynf <- normaliseHoles env ety
                                                 pure (Just !(toFullNames etynf)))
                                       exp
                    pure ("Checking application of " ++ show !(getFullName n) ++
                          " (" ++ show n ++ ")" ++
                          " to " ++ show expargs ++ "\n\tFunction type " ++
                          (show !(toFullNames fnty)) ++ "\n\tExpected app type "
                                ++ show exptyt))
        let fn = case lookup n (names nest) of
                      Just (Just n', _) => n'
                      _ => n
        normalisePrims prims env
           !(checkAppWith rig elabinfo nest env fc ntm nty (Just fn, arglen) expargs autoargs namedargs False exp)
  where

    -- If the term is an application of a primitive conversion (fromInteger etc)
    -- and it's applied to a constant, fully normalise the term.
    normalisePrims : {vs : _} ->
                     List Name -> Env Term vs ->
                     (Term vs, Glued vs) ->
                     Core (Term vs, Glued vs)
    normalisePrims prims env res
        = do tm <- Evaluate.normalisePrims (`boundSafe` elabMode elabinfo)
                                            isIPrimVal
                                            (onLHS (elabMode elabinfo))
                                            prims n (cast {to=SnocList RawImp} expargs) (fst res) env
             pure (fromMaybe (fst res) tm, snd res)
      where
        boundSafe : Constant -> ElabMode -> Bool
        boundSafe _ (InLHS _) = True -- always need to expand on LHS
        -- only do this for relatively small bounds.
        -- Once it gets too big, we might be making the term
        -- bigger than it would have been without evaluating!
        boundSafe (BI x) _ = abs x < 100
        boundSafe (Str str) _ = length str < 10
        boundSafe _ _ = True

    updateElabInfo : List Name -> ElabMode -> Name ->
                     List RawImp -> ElabInfo -> Core ElabInfo
    -- If it's a primitive function applied to a constant on the LHS, treat it
    -- as an expression because we'll normalise the function away and match on
    -- the result
    updateElabInfo prims (InLHS _) n [IPrimVal fc c] elabinfo =
        do if isPrimName prims !(getFullName n)
              then pure ({ elabMode := InExpr } elabinfo)
              else pure elabinfo
    updateElabInfo _ _ _ _ info = pure info

checkApp rig elabinfo nest env fc fn expargs autoargs namedargs exp
   = do (fntm, fnty_in) <- checkImp rig elabinfo nest env fn Nothing
        fnty <- expand fnty_in
        checkAppWith rig elabinfo nest env fc fntm fnty (Nothing, 0) expargs autoargs namedargs False exp
