module TTImp.Elab.RunElab

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.Metadata
import Core.Evaluate
import Core.Options
import Core.Reflect
import Core.Unify
import Core.TT

import TTImp.Elab.Check
import TTImp.Elab.Delayed
import TTImp.Reflect
import TTImp.TTImp
import TTImp.TTImp.Functor
import TTImp.Unelab

import Data.SnocList

%default covering

record NameInfo where
  constructor MkNameInfo
  nametype : NameType

lookupNameInfo : Name -> Context -> Core (List (Name, NameInfo))
lookupNameInfo n ctxt
    = do res <- lookupCtxtName n ctxt
         pure (map (\ (n, i, gd) =>
                      (n, MkNameInfo { nametype = getNameType (definition gd) } ))
                   res)
  where
    getNameType : Def -> NameType
    getNameType (DCon _ t a) = DataCon t a
    getNameType (TCon t a) = TyCon a
    getNameType _ = Func

Reflect NameInfo where
  reflect fc defs lhs env inf
      = do nt <- reflect fc defs lhs env (nametype inf)
           appConTop fc defs (reflectiontt "MkNameInfo") [nt]

export
elabScript : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto u : Ref UST UState} ->
             RigCount -> FC -> NestedNames vars ->
             Env Term vars -> NF vars -> Maybe (Glued vars) ->
             Core (Glued vars)
elabScript rig fc nest env script@(VDCon nfc nm t ar args) exp
    = do defs <- get Ctxt
         fnm <- toFullNames nm
         case fnm of
              NS ns (UN (Basic n))
                 => if ns == reflectionNS
                      then elabCon defs n (cast !(traverseSnocList value args))
                             `catch` \case -- wrap into `RunElabFail` any non-elab error
                               e@(BadRunElab _ _ _ _) => throw e
                               e@(RunElabFail _)      => throw e
                               e                      => throw $ RunElabFail e
                      else failWith $ "bad reflection namespace " ++ show ns
              _ => failWith $ "bad fullnames " ++ show fnm
  where
    failWith : String -> Core a
    failWith desc
      = throw (BadRunElab fc env !(quote env script) desc)

    scriptRet : Reflect a => a -> Core (Glued vars)
    scriptRet tm
        = do defs <- get Ctxt
             nf env !(reflect fc defs False env tm)

    elabCon : Defs -> String -> List (Glued vars) -> Core (Glued vars)
    elabCon defs "Pure" [_,val] = pure val
    elabCon defs "Bind" [_,_,act,k]
        -- act : Elab A
        -- k : A -> Elab B
        -- 1) Run elabScript on act stripping off Elab
        -- 2) Evaluate the resulting act
        -- 3) apply k to the result of (2)
        -- 4) Run elabScript on the result stripping off Elab
        = do act <- elabScript rig fc nest env !(expand act) exp
             r <- apply fc k top (pure act)
             elabScript rig fc nest env !(expand r) exp
    elabCon defs "Fail" [_, mbfc, msg]
        = do msg' <- expand msg
             let customFC = case !(expand mbfc >>= reify defs) of
                               EmptyFC => fc
                               x       => x
             throw $ RunElabFail $ GenericMsg customFC !(reify defs msg')
    elabCon defs "Try" [_, elab1, elab2]
        = tryUnify (do constart <- getNextEntry
                       res <- elabScript rig fc nest env !(expand elab1) exp
                       -- We ensure that all of the constraints introduced during the elab script
                       -- have been solved. This guarantees that we do not mistakenly succeed even
                       -- though e.g. a proof search got delayed.
                       solveConstraintsAfter constart inTerm LastChance
                       pure res)
                   (elabScript rig fc nest env !(expand elab2) exp)
    elabCon defs "LogMsg" [topic, verb, str]
        = do topic' <- expand topic
             verb' <- expand verb
             unverifiedLogC !(reify defs topic') !(reify defs verb') $
                  do str' <- expand str
                     reify defs str'
             scriptRet ()
    elabCon defs "LogTerm" [topic, verb, str, tm]
        = do topic' <- expand topic
             verb' <- expand verb
             unverifiedLogC !(reify defs topic') !(reify defs verb') $
                  do str' <- expand str
                     tm' <- expand tm
                     pure $ !(reify defs str') ++ ": " ++
                             show (the RawImp !(reify defs tm'))
             scriptRet ()
    elabCon defs "Check" [exp, ttimp]
        = do ttimp' <- expand ttimp
             tidx <- resolveName (UN $ Basic "[elaborator script]")
             e <- newRef EST (initEState tidx env)
             (checktm, _) <- runDelays (const True) $
                     check rig (initElabInfo InExpr) nest env !(reify defs ttimp')
                           (Just exp)
             nf env checktm
    elabCon defs "Quote" [exp, tm]
        = do tm' <- expand tm
             defs <- get Ctxt
             scriptRet $ map rawName !(unelabUniqueBinders env !(quote env tm'))
    elabCon defs "Lambda" [x, _, scope]
        = do VBind bfc x (Lam fc' c p ty) sc <- expand scope
                   | _ => failWith "Not a lambda"
             n <- genVarName "x"
             sc' <- sc (pure (vRef bfc Bound n))
             qsc <- quote env sc'
             let lamsc = refToLocal n x qsc
             qp <- quotePi p
             qty <- quote env ty
             let env' = env :< Lam fc' c qp qty
             runsc <- elabScript rig fc (weaken nest) env'
                                 !(expand !(nf env' lamsc)) Nothing
             nf env (Bind bfc x (Lam fc' c qp qty) !(quote env' runsc))
       where
         quotePi : PiInfo (Glued vars) -> Core (PiInfo (Term vars))
         quotePi Explicit = pure Explicit
         quotePi Implicit = pure Implicit
         quotePi AutoImplicit = pure AutoImplicit
         quotePi (DefImplicit t) = failWith "Can't add default lambda"
    elabCon defs "Goal" []
        = do let Just gty = exp
                 | Nothing => nf env
                                !(reflect fc defs False env (the (Maybe RawImp) Nothing))
             ty <- quote env gty
             scriptRet (Just $ map rawName $ !(unelabUniqueBinders env ty))
    elabCon defs "LocalVars" []
        = scriptRet (the (List Name) (cast vars))
    elabCon defs "GenSym" [str]
        = do str' <- expand str
             n <- genVarName !(reify defs str')
             scriptRet n
    elabCon defs "InCurrentNS" [n]
        = do n' <- expand n
             nsn <- inCurrentNS !(reify defs n')
             scriptRet nsn
    elabCon defs "GetType" [n]
        = do n' <- expand n
             res <- lookupTyName !(reify defs n') (gamma defs)
             scriptRet !(traverse unelabType res)
      where
        unelabType : (Name, Int, ClosedTerm) -> Core (Name, RawImp)
        unelabType (n, _, ty)
            = pure (n, map rawName !(unelabUniqueBinders [<] ty))
    elabCon defs "GetInfo" [n]
        = do n' <- expand n
             res <- lookupNameInfo !(reify defs n') (gamma defs)
             scriptRet res
    elabCon defs "GetLocalType" [n]
        = do n' <- expand n
             n <- reify defs n'
             case defined n env of
                  Just (MkIsDefined rigb lv) =>
                       do let binder = getBinder lv env
                          let bty = binderType binder
                          scriptRet $ map rawName !(unelabUniqueBinders env bty)
                  _ => failWith $ show n ++ " is not a local variable"
    elabCon defs "GetCons" [n]
        = do n' <- expand n
             cn <- reify defs n'
             Just (TCon ti _) <-
                     lookupDefExact cn (gamma defs)
                 | _ => failWith $ show cn ++ " is not a type"
             scriptRet (datacons ti)
    elabCon defs "Declare" [d]
        = do d' <- expand d
             decls <- reify defs d'
             traverse_ (processDecl [] (MkNested []) [<]) decls
             scriptRet ()
    elabCon defs n args = failWith $ "unexpected Elab constructor " ++ n ++
                                          ", or incorrect count of arguments: " ++ show (length args)
elabScript rig fc nest env script exp
    = throw (BadRunElab fc env !(quote env script) "script is not a data value")

export
checkRunElab : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               {auto m : Ref MD Metadata} ->
               {auto u : Ref UST UState} ->
               {auto e : Ref EST (EState vars)} ->
               RigCount -> ElabInfo ->
               NestedNames vars -> Env Term vars ->
               FC -> RawImp -> Maybe (Glued vars) ->
               Core (Term vars, Glued vars)
checkRunElab rig elabinfo nest env fc script exp
    = do expected <- mkExpected exp
         defs <- get Ctxt
         unless (isExtension ElabReflection defs) $
             throw (GenericMsg fc "%language ElabReflection not enabled")
         let n = NS reflectionNS (UN $ Basic "Elab")
         elabtt <- appConTop fc defs n [expected]
         (stm, sty) <- runDelays (const True) $
                           check rig elabinfo nest env script (Just !(nf env elabtt))
         solveConstraints inTerm Normal
         defs <- get Ctxt -- checking might have resolved some holes
         ntm <- elabScript rig fc nest env
                           !(expand !(nf env stm)) (Just !(nf env expected))
         defs <- get Ctxt -- might have updated as part of the script
         pure (!(quote env ntm), !(nf env expected))
  where
    mkExpected : Maybe (Glued vars) -> Core (Term vars)
    mkExpected (Just ty) = pure !(quote env ty)
    mkExpected Nothing
        = do nm <- genName "scriptTy"
             u <- uniVar fc
             metaVar fc erased env nm (TType fc u)
