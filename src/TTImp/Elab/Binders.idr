module TTImp.Elab.Binders

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.Metadata
import Core.Evaluate
import Core.Unify
import Core.TT

import TTImp.Elab.Check
import TTImp.Elab.Delayed
import TTImp.TTImp

%default covering

-- Drop the name from the nested function declarations. We do this when
-- going into a new scope, so that we're resolving to the most recently
-- bound name.
export
dropName : Name -> NestedNames vars -> NestedNames vars
dropName n nest = { names $= drop } nest
  where
    drop : List (Name, a) -> List (Name, a)
    drop [] = []
    drop ((x, y) :: xs)
        = if x == n then drop xs
             else (x, y) :: drop xs

checkPiInfo : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto u : Ref UST UState} ->
              {auto e : Ref EST (EState vars)} ->
              RigCount -> ElabInfo -> NestedNames vars -> Env Term vars ->
              PiInfo RawImp -> (expTy : Maybe (Glued vars)) ->
              Core (PiInfo (Term vars))
checkPiInfo rig elabinfo nest env Explicit exp = pure Explicit
checkPiInfo rig elabinfo nest env Implicit exp = pure Implicit
checkPiInfo rig elabinfo nest env AutoImplicit exp = pure AutoImplicit
checkPiInfo rig elabinfo nest env (DefImplicit t) exp
    = do (tv, _) <- check rig elabinfo nest env t exp
         pure (DefImplicit tv)

export
checkPi : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          {auto m : Ref MD Metadata} ->
          {auto u : Ref UST UState} ->
          {auto e : Ref EST (EState vars)} ->
          RigCount -> ElabInfo ->
          NestedNames vars -> Env Term vars ->
          FC ->
          RigCount -> PiInfo RawImp -> (n : Name) ->
          (argTy : RawImp) -> (retTy : RawImp) ->
          (expTy : Maybe (Glued vars)) ->
          Core (Term vars, Glued vars)
checkPi rig elabinfo nest env fc rigf info n argTy retTy expTy
    = do let pirig = getRig (elabMode elabinfo)
         tyu <- uniVar fc
         (tyv, tyt) <- check pirig elabinfo nest env argTy
                             (Just (VType fc tyu))
         info' <- checkPiInfo rigf elabinfo nest env info (Just !(nf env tyv))
         let env' : Env Term (_ :< n) = env :< Pi fc rigf info' tyv
         let nest' = weaken (dropName n nest)
         scu <- uniVar fc
         (scopev, scopet) <-
            inScope fc env' (\e' =>
              check {e=e'} pirig elabinfo nest' env' retTy (Just (VType fc scu)))
         -- TODO Cumulativity: tyu <= max, scu <= max
         piu <- uniVar fc
         checkExp rig elabinfo env fc (Bind fc n (Pi (getFC argTy) rigf info' tyv) scopev) (VType fc piu) expTy
  where
    -- Might want to match on the LHS, so use the context rig, otherwise
    -- it's always erased
    getRig : ElabMode -> RigCount
    getRig (InLHS _) = rig
    getRig _ = erased

findLamRig : {auto c : Ref Ctxt Defs} ->
             Maybe (Glued vars) -> Core RigCount
findLamRig Nothing = pure top
findLamRig (Just expty)
    = do tynf <- expand expty
         case tynf of
              VBind _ _ (Pi _ c _ _) sc => pure c
              _ => pure top

inferLambda : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto u : Ref UST UState} ->
              {auto e : Ref EST (EState vars)} ->
              RigCount -> ElabInfo ->
              NestedNames vars -> Env Term vars ->
              FC ->
              RigCount -> PiInfo RawImp -> (n : Name) ->
              (argTy : RawImp) -> (scope : RawImp) ->
              (expTy : Maybe (Glued vars)) ->
              Core (Term vars, Glued vars)
inferLambda rig elabinfo nest env fc rigl info n argTy scope expTy
    = do rigb_in <- findLamRig expTy
         let rigb = rigb_in `glb` rigl
         u <- uniVar fc
         (tyv, tyt) <- check erased elabinfo nest env argTy (Just (VType fc u))
         info' <- checkPiInfo rigl elabinfo nest env info (Just !(nf env tyv))
         let env' : Env Term (_ :< n) = env :< Lam fc rigb info' tyv
         let nest' = weaken (dropName n nest)
         (scopev, scopet) <- inScope fc env' (\e' =>
                                check {e=e'} rig elabinfo
                                      nest' env' scope Nothing)
         lamty <- nf env (Bind fc n (Pi fc rigb info' tyv) !(quote env' scopet))
         logNF "elab.binder" 5 "Inferred lambda type" env lamty
         maybe (pure ())
               (logNF "elab.binder" 5 "Expected lambda type" env) expTy
         checkExp rig elabinfo env fc
                  (Bind fc n (Lam fc rigb info' tyv) scopev)
                  lamty expTy

export
checkLambda : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto m : Ref MD Metadata} ->
              {auto u : Ref UST UState} ->
              {auto e : Ref EST (EState vars)} ->
              RigCount -> ElabInfo ->
              NestedNames vars -> Env Term vars ->
              FC ->
              RigCount -> PiInfo RawImp -> (n : Name) ->
              (argTy : RawImp) -> (scope : RawImp) ->
              (expTy : Maybe (Glued vars)) ->
              Core (Term vars, Glued vars)
checkLambda rig_in elabinfo nest env fc rigl info n argTy scope Nothing
    = let rig = if isErased rig_in then erased else linear in
          inferLambda rig elabinfo nest env fc rigl info n argTy scope Nothing
checkLambda rig_in elabinfo nest env fc rigl info n argTy scope (Just expty_in)
    = do let rig = if isErased rig_in then erased else linear
         let solvemode = case elabMode elabinfo of
                              InLHS _ => inLHS
                              _ => inTerm
         solveConstraints solvemode Normal
         expty <- quoteOnePi env !(expand expty_in)
         case expty of
              Bind bfc bn (Pi fc' c _ pty) psc =>
                 do u <- uniVar fc'
                    (tyv, tyt) <- check erased elabinfo nest env
                                        argTy (Just (VType fc u))
                    info' <- checkPiInfo rigl elabinfo nest env info (Just !(nf env tyv))
                    let rigb = rigl `glb` c
                    let env' : Env Term (_ :< n) = env :< Lam fc rigb info' tyv
                    ignore $ convert fc elabinfo env !(nf env tyv) !(nf env pty)
                    let nest' = weaken (dropName n nest)
                    let scopetTm = renameTop n psc
                    scopet <- nf env' scopetTm
                    (scopev, _) <-
                       inScope fc env' (\e' =>
                          check {e=e'} rig elabinfo nest' env' scope
                                (Just scopet)) -- !(nf env' (renameTop n psc))))
                    logTermNF "elab.binder" 10 "Lambda type" env expty
                    logNF "elab.binder" 10 "Got scope type" env' scopet

                    -- Currently, the fc a PLam holds (and that ILam gets as a consequence)
                    -- is the file context of the argument to the lambda. This fits nicely
                    -- in this exact use, but is likely a bug.
                    log "metadata.names" 7 "checkLambda is adding ↓"
                    addNameType fc n env pty -- Add the type of the argument to the metadata

                    -- We've already checked the argument and scope types,
                    -- so we just need to check multiplicities
                    defs <- get Ctxt
                    when (rigb /= c) $
                           throw (CantConvert fc defs env
                                    (Bind fc n (Pi fc' rigb info' tyv) scopetTm)
                                    (Bind fc bn (Pi fc' c info' pty) psc))

                    pure (Bind fc n (Lam fc' rigb info' tyv) scopev,
                          !(nf env (Bind fc n (Pi fc' rigb info' tyv) scopetTm)))
              _ => inferLambda rig elabinfo nest env fc rigl info n argTy scope (Just expty_in)

weakenExp : {x, vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            Env Term (vars :< x) ->
            Maybe (Glued vars) -> Core (Maybe (Glued (vars :< x)))
weakenExp env Nothing = pure Nothing
weakenExp env@(env' :< _) (Just gtm)
    = do tm <- quote env' gtm
         pure (Just !(nf env (weaken tm)))

export
checkLet : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto m : Ref MD Metadata} ->
           {auto u : Ref UST UState} ->
           {auto e : Ref EST (EState vars)} ->
           RigCount -> ElabInfo ->
           NestedNames vars -> Env Term vars ->
           FC -> (lhsFC : FC) -> RigCount -> (n : Name) ->
           (nTy : RawImp) -> (nVal : RawImp) -> (scope : RawImp) ->
           (expTy : Maybe (Glued vars)) ->
           Core (Term vars, Glued vars)
checkLet rigc_in elabinfo nest env fc lhsFC rigl n nTy nVal scope expty {vars}
    = do let rigc = if isErased rigc_in then erased else linear
         u <- uniVar fc
         (tyv, tyt) <- check erased elabinfo nest env nTy (Just (VType fc u))
         -- Try checking at the given multiplicity; if that doesn't work,
         -- try checking at Rig1 (meaning that we're using a linear variable
         -- so the resulting binding should be linear)
         -- Also elaborate any case blocks in the value via runDelays
         (valv, valt, rigb) <- handle
              (do c <- runDelays (==CaseBlock) $ check (rigl |*| rigc)
                             elabinfo nest env nVal (Just !(nf env tyv))
                  pure (fst c, snd c, rigl |*| rigc))
              (\err => case linearErr err of
                            Just r
                              => do branchOne
                                     (do c <- runDelays (==CaseBlock) $ check linear elabinfo
                                                  nest env nVal (Just !(nf env tyv))
                                         pure (fst c, snd c, linear))
                                     (do c <- check (rigl |*| rigc)
                                                  elabinfo
                                                  nest env nVal (Just !(nf env tyv))
                                         pure (fst c, snd c, rigMult rigl rigc))
                                     r
                            _ => do c <- check (rigl |*| rigc)
                                               elabinfo
                                               nest env nVal (Just !(nf env tyv))
                                    pure (fst c, snd c, rigl |*| rigc))
         let env' : Env Term (_ :< n) = env :< Lam fc rigb Explicit tyv
         let nest' = weaken (dropName n nest)
         expScope <- weakenExp env' expty
         (scopev, gscopet) <-
            inScope fc env' (\e' =>
              check {e=e'} rigc elabinfo nest' env' scope expScope)
         scopet <- quote env' gscopet

         -- No need to 'checkExp' here - we've already checked scopet
         -- against the expected type when checking the scope, so just
         -- build the term directly

         -- Add the lhs of the let to metadata
         log "metadata.names" 7 $ "checkLet is adding ↓"
         addNameType lhsFC n env tyv

         pure (Bind fc n (Let fc rigb valv tyv) scopev,
               !(nf env (Bind fc n (Let fc rigb valv tyv) scopet)))
  where
    linearErr : Error -> Maybe RigCount
    linearErr (LinearMisuse _ _ r _) = Just r
    linearErr (InType _ _ e) = linearErr e
    linearErr (InCon _ _ e) = linearErr e
    linearErr (InLHS _ _ e) = linearErr e
    linearErr (InRHS _ _ e) = linearErr e
    linearErr _ = Nothing
