module Core.Unify.Unify

import Core.Core
import Core.Context
import Core.Context.Log
import Core.TT
import Core.Evaluate
import Core.Unify.SolveMeta
import Core.Unify.State

import Data.List
import Data.SnocList
import Data.Vect

import Libraries.Data.IntMap
import Libraries.Data.NameMap

parameters {auto c : Ref Ctxt Defs}
  export
  setInvertible : FC -> Name -> Core ()
  setInvertible fc n
      = do defs <- get Ctxt
           Just gdef <- lookupCtxtExact n (gamma defs)
                | Nothing => undefinedName fc n
           ignore $ addDef n ({ invertible := True } gdef)

  isDefInvertible : FC -> Int -> Core Bool
  isDefInvertible fc i
      = do defs <- get Ctxt
           Just gdef <- lookupCtxtExact (Resolved i) (gamma defs)
                | Nothing => throw (UndefinedName fc (Resolved i))
           pure (invertible gdef)

third : (s, t, u) -> u
third (x, y, z) = z

parameters {auto c : Ref Ctxt Defs} {auto c : Ref UST UState}
  namespace Value
    export
    unify : {vars : _} ->
            UnifyInfo -> FC -> Env Term vars ->
            Value vars -> Value vars -> Core UnifyResult
    export
    unifyWithLazy : {vars : _} ->
            UnifyInfo -> FC -> Env Term vars ->
            Value vars -> Value vars -> Core UnifyResult

  namespace Term
    export
    unify : {vars : _} ->
            UnifyInfo -> FC -> Env Term vars ->
            Term vars -> Term vars -> Core UnifyResult
    export
    unifyWithLazy : {vars : _} ->
            UnifyInfo -> FC -> Env Term vars ->
            Term vars -> Term vars -> Core UnifyResult

  convertError : {vars : _} ->
            FC -> Env Term vars -> Value vars -> Value vars -> Core a
  convertError loc env x y
      = do defs <- get Ctxt
           throw (CantConvert loc defs env !(quote env x) !(quote env y))

  convertErrorS : {vars : _} ->
            Bool -> FC -> Env Term vars -> Value vars -> Value vars ->
            Core a
  convertErrorS s loc env x y
      = if s then convertError loc env y x
             else convertError loc env x y

  postpone : {vars : _} ->
             FC -> UnifyInfo -> String ->
             Env Term vars -> Value vars -> Value vars -> Core UnifyResult
  postpone loc mode logstr env x y
      = do defs <- get Ctxt
           xtm <- quote env x
           ytm <- quote env y
           logC "unify.postpone" 10 $
                do xf <- toFullNames xtm
                   yf <- toFullNames ytm
                   pure (logstr ++ ": " ++ show xf ++ " =?= " ++ show yf)

           -- If we're blocked because a name is undefined, give up
           checkDefined defs x
           checkDefined defs y

           c <- addConstraint (MkConstraint loc (atTop mode) env xtm ytm)
           log "unify.postpone" 10 $
                   show c ++ " NEW CONSTRAINT " ++ show loc
           logTerm "unify.postpone" 10 "X" xtm
           logTerm "unify.postpone" 10 "Y" ytm
           pure (constrain c)
    where
      checkDefined : Defs -> Value vars -> Core ()
      checkDefined defs (VApp _ _ n _ _)
          = do Just _ <- lookupCtxtExact n (gamma defs)
                    | _ => undefinedName loc n
               pure ()
      checkDefined _ _ = pure ()

      undefinedN : Name -> Core Bool
      undefinedN n
          = do defs <- get Ctxt
               pure $ case !(lookupDefExact n (gamma defs)) of
                    Just (Hole _) => True
                    Just (BySearch _ _ _) => True
                    Just (Guess _ _ _) => True
                    _ => False

  postponeS : {vars : _} ->
              Bool -> FC -> UnifyInfo -> String -> Env Term vars ->
              Value vars -> Value vars ->
              Core UnifyResult
  postponeS s loc mode logstr env x y
      = if s then postpone loc (lower mode) logstr env y x
             else postpone loc mode logstr env x y

  postponePatVar : {vars : _} ->
                   (swaporder : Bool) ->
                   UnifyInfo -> FC -> Env Term vars ->
                   (metaname : Name) -> (metaref : Int) ->
                   (margs : List (RigCount, Value vars)) ->
                   (margs' : Spine vars) ->
                   (soln : Value vars) ->
                   Core UnifyResult
  postponePatVar swap mode fc env mname mref margs margs' tm
      = do let x = VMeta fc mname mref margs margs' (pure Nothing)
           if !(convert env x tm)
              then pure success
              else postponeS swap fc mode "Not in pattern fragment" env
                             x tm

  unifyArgs : {vars : _} ->
              UnifyInfo -> FC -> Env Term vars ->
              List (Value vars) -> List (Value vars) ->
              Core UnifyResult
  unifyArgs mode loc env [] [] = pure success
  unifyArgs mode loc env (cx :: cxs) (cy :: cys)
      = do -- Do later arguments first, since they may depend on earlier
           -- arguments and use their solutions.
           cs <- unifyArgs mode loc env cxs cys
           res <- unify (lower mode) loc env cx cy
           pure (union res cs)
  unifyArgs mode loc env _ _ = ufail loc ""

  unifySpine : {vars : _} ->
              UnifyInfo -> FC -> Env Term vars ->
              Spine vars -> Spine vars ->
              Core UnifyResult
  unifySpine mode fc env [<] [<] = pure success
  unifySpine mode fc env (cxs :< (_, _, cx)) (cys :< (_, _, cy))
      = do cs <- unify (lower mode) fc env cx cy
           res <- unifySpine mode fc env cxs cys
           pure (union cs res)
  unifySpine mode fc env _ _ = ufail fc ""

  convertSpine : {vars : _} ->
              FC -> Env Term vars ->
              Spine vars -> Spine vars ->
              Core Bool
  convertSpine fc env [<] [<] = pure True
  convertSpine fc env (cxs :< (_, _, cx)) (cys :< (_, _, cy))
      = if !(convert env cx cy)
           then convertSpine fc env cxs cys
           else pure False
  convertSpine fc env _ _ = pure False

  unifyIfEq : {vars : _} ->
              (postpone : Bool) ->
              FC -> UnifyInfo -> Env Term vars -> Value vars -> Value vars ->
              Core UnifyResult
  unifyIfEq post loc mode env x y
        = if !(convert env x y)
             then pure success
             else if post
                     then postpone loc mode ("Postponing unifyIfEq " ++
                                                 show (atTop mode)) env x y
                     else convertError loc env x y

  spineToValues : Spine vars -> List (Value vars)
  spineToValues sp = toList (map third sp)

  headsConvert : {vars : _} ->
                 UnifyInfo ->
                 FC -> Env Term vars ->
                 Maybe (SnocList (Value vars)) -> Maybe (SnocList (Value vars)) ->
                 Core Bool
  headsConvert mode fc env (Just vs) (Just ns)
      = case (vs, ns) of
             (_ :< v, _ :< n) =>
                do logNF "unify.head" 10 "Unifying head" env v
                   logNF "unify.head" 10 ".........with" env n
                   res <- unify mode fc env v n
                   -- If there's constraints, we postpone the whole equation
                   -- so no need to record them
                   pure (isNil (constraints res))
             _ => pure False
  headsConvert mode fc env _ _
      = do log "unify.head" 10 "Nothing to convert"
           pure True

  getArgTypes : {vars : _} ->
                (fnType : Value vars) -> SnocList (Value vars) ->
                Core (Maybe (SnocList (Value vars)))
  getArgTypes (VBind _ n (Pi _ _ _ ty) sc) (as :< a)
     = do Just scTys <- getArgTypes !(expand !(sc a)) as
               | Nothing => pure Nothing
          pure (Just (scTys :< ty))
  getArgTypes _ [<] = pure (Just [<])
  getArgTypes _ _ = pure Nothing

  unifyInvertible : {vars : _} ->
                    (swaporder : Bool) ->
                    UnifyInfo -> FC -> Env Term vars ->
                    (metaname : Name) -> (metaref : Int) ->
                    (args : List (RigCount, Value vars)) ->
                    (sp : Spine vars) ->
                    Maybe (Term [<]) ->
                    (Spine vars -> Value vars) ->
                    Spine vars ->
                    Core UnifyResult
  unifyInvertible swap mode fc env mname mref args sp nty con args'
      = do defs <- get Ctxt
           -- Get the types of the arguments to ensure that the rightmost
           -- argument types match up
           Just vty <- lookupTyExact (Resolved mref) (gamma defs)
                | Nothing => ufail fc ("No such metavariable " ++ show mname)
           vargTys <- getArgTypes !(expand !(nf env (embed vty)))
                                  (cast (map snd args) ++ map third sp) --  ++ sp)
           nargTys <- maybe (pure Nothing)
                            (\ty => getArgTypes !(expand !(nf env (embed ty)))
                                                $ map third args')
                            nty
--            -- If the rightmost arguments have the same type, or we don't
--            -- know the types of the arguments, we'll get on with it.
           if !(headsConvert mode fc env vargTys nargTys)
              then
                -- Unify the rightmost arguments, with the goal of turning the
                -- hole application into a pattern form
                case (sp, args') of
                     (hargs :< h, fargs :< f) =>
                        tryUnify
                          (if not swap then
                              do ures <- unify mode fc env (third h) (third f)
                                 log "unify.invertible" 10 $ "Constraints " ++ show (constraints ures)
                                 uargs <- unify mode fc env
                                                (VMeta fc mname mref args hargs (pure Nothing))
                                                (con fargs)
                                 pure (union ures uargs)
                             else
                              do log "unify.invertible" 10 "Unifying invertible"
                                 ures <- unify mode fc env (third f) (third h)
                                 log "unify.invertible" 10 $ "Constraints " ++ show (constraints ures)
                                 uargs <- unify mode fc env
                                                (con fargs)
                                                (VMeta fc mname mref args hargs (pure Nothing))
                                 pure (union ures uargs))
                          (postponeS swap fc mode "Postponing hole application [1]" env
                                (VMeta fc mname mref args sp (pure Nothing))
                                (con args'))
                     _ => postponeS swap fc mode "Postponing hole application [2]" env
                                (VMeta fc mname mref args sp (pure Nothing))
                                (con args')
              else -- TODO: Cancellable function applications
                   postpone fc mode "Postponing hole application [3]" env
                            (VMeta fc mname mref args sp (pure Nothing)) (con args')

  -- Unify a hole application - we have already checked that the hole is
  -- invertible (i.e. it's a determining argument to a proof search where
  -- it is a constructor or something else invertible in each case)
  unifyHoleApp : {vars : _} ->
                 (swaporder : Bool) ->
                 UnifyInfo -> FC -> Env Term vars ->
                 (metaname : Name) -> (metaref : Int) ->
                 (args : List (RigCount, Value vars)) ->
                 (sp : Spine vars) ->
                 Value vars ->
                 Core UnifyResult
  unifyHoleApp swap mode fc env mname mref args sp (VTCon nfc n a args')
      = do defs <- get Ctxt
           mty <- lookupTyExact n (gamma defs)
           unifyInvertible swap (lower mode) fc env
                           mname mref args sp mty (VTCon nfc n a) args'
  unifyHoleApp swap mode fc env mname mref args sp (VDCon nfc n t a args')
      = do defs <- get Ctxt
           mty <- lookupTyExact n (gamma defs)
           unifyInvertible swap (lower mode) fc env
                           mname mref args sp mty (VDCon nfc n t a) args'
  unifyHoleApp swap mode loc env mname mref args sp (VLocal nfc r idx p args')
      = unifyInvertible swap (lower mode) loc env
                        mname mref args sp Nothing (VLocal nfc r idx p) args'
  unifyHoleApp swap mode fc env mname mref args sp tm@(VMeta nfc n i margs2 args2' val)
      = do defs <- get Ctxt
           Just mdef <- lookupCtxtExact (Resolved i) (gamma defs)
                | Nothing => undefinedName nfc mname
           let inv = isPatName n || invertible mdef
           if inv
              then unifyInvertible swap (lower mode) fc env
                                   mname mref args sp Nothing
                                   (\t => VMeta nfc n i margs2 t val) args2'
              else postponeS swap fc mode "Postponing hole application" env
                             (VMeta fc mname mref args sp (pure Nothing)) tm
    where
      isPatName : Name -> Bool
      isPatName (PV _ _) = True
      isPatName _ = False
  unifyHoleApp swap mode fc env mname mref args sp tm
      = postponeS swap fc mode "Postponing hole application" env
                 (VMeta fc mname mref args sp (pure Nothing)) tm

  -- Solve a metavariable application (that is, the name applied the to
  -- args and spine) with the given solution.
  -- Also given the results we got from 'patternEnv' that tells us how to
  -- instantiate the environment in the solution
  solveHole : {newvars, vars : _} ->
              FC -> UnifyInfo -> Env Term vars ->
              (metaname : Name) -> (metaref : Int) ->
              (args : List (RigCount, Value vars)) ->
              (sp : Spine vars) ->
              SnocList (Var newvars) ->
              SubVars newvars vars ->
              (solfull : Term vars) -> -- Original solution
              (soln : Term newvars) -> -- Solution with shrunk environment
              (solnf : Value vars) ->
              Core (Maybe UnifyResult)
  solveHole fc mode env mname mref margs margs' locs submv solfull stm solnf
      = do defs <- get Ctxt
           ust <- get UST
           if solutionHeadSame solnf || inNoSolve mref (noSolve ust)
              then pure $ Just success
              else do Just hdef <- lookupCtxtExact (Resolved mref) (gamma defs)
                           | Nothing => throw (InternalError ("Can't happen: Lost hole " ++ show mname))
                      progress <- tryInstantiate fc mode env mname mref (length margs) hdef (toList locs) solfull stm
                      pure $ toMaybe progress (solvedHole mref)
    where
      inNoSolve : Int -> IntMap () -> Bool
      inNoSolve i ns
          = case lookup i ns of
                 Nothing => False
                 Just _ => True

      -- Only need to check the head metavar is the same, we've already
      -- checked the rest if they are the same (and we couldn't instantiate it
      -- anyway...)
      -- Also the solution is expanded by now (via Evaluate.Value.expand)
      solutionHeadSame : Value vars -> Bool
      solutionHeadSame (VMeta _ _ shead _ _ _) = shead == mref
      solutionHeadSame _ = False

  -- Try to solve 'metaname' applied to all the arguments with the
  -- given solution
  unifyHole : {vars : _} ->
              (swaporder : Bool) ->
              UnifyInfo -> FC -> Env Term vars ->
              FC -> (metaname : Name) -> (metaref : Int) ->
              (args : List (RigCount, Value vars)) ->
              (sp : Spine vars) ->
              (soln : Value vars) ->
              Core UnifyResult
  unifyHole swap mode fc env nfc mname mref args sp tmnf
      = do let margs = cast (map snd args)
           let margs' = map third sp
           let pargs = if isLin margs' then margs else margs ++ margs'
           defs <- get Ctxt
           case !(patternEnv env pargs) of
                Nothing =>
                  do Just hdef <- lookupCtxtExact (Resolved mref) (gamma defs)
                        | _ => postponePatVar swap mode fc env mname mref args sp tmnf
                     let Hole _ = definition hdef
                        | _ => postponePatVar swap mode fc env mname mref args sp tmnf
                     if invertible hdef
                        then unifyHoleApp swap mode fc env mname mref args sp tmnf
                        else postponePatVar swap mode fc env mname mref args sp tmnf
                Just (newvars ** (locs, submv)) =>
                  do Just hdef <- lookupCtxtExact (Resolved mref) (gamma defs)
                         | _ => postponePatVar swap mode fc env mname mref args sp tmnf
                     let Hole _ = definition hdef
                         | _ => postponeS swap fc mode "Delayed hole" env
                                          (VMeta fc mname mref args sp (pure Nothing))
                                          tmnf
                     tm <- quote env tmnf
                     Just tm <- occursCheck fc env mode mname tm
                         | _ => postponeS swap fc mode "Occurs check failed" env
                                          (VMeta fc mname mref args sp (pure Nothing))
                                          tmnf
                     let solveOrElsePostpone : Term newvars -> Core UnifyResult
                         solveOrElsePostpone stm = do
                           mbResult <- solveHole fc mode env mname mref
                                            args sp locs submv
                                            tm stm tmnf
                           flip fromMaybe (pure <$> mbResult) $
                             postponeS swap fc mode "Can't instantiate" env
                                       (VMeta fc mname mref args sp (pure Nothing))
                                       tmnf
                     case shrinkTerm tm submv of
                          Just stm => solveOrElsePostpone stm
                          Nothing =>
                            do tm' <- quote env tmnf
                               case shrinkTerm tm' submv of
                                    Nothing => postponeS swap fc mode "Can't shrink" env
                                                 (VMeta fc mname mref args sp (pure Nothing))
                                                 tmnf
                                    Just stm => solveOrElsePostpone stm

  -- Main bit of unification, decomposing unification problems into
  -- sub-problems and solving metavariables where appropriate
  unifyNoEta : {vars : _} ->
          UnifyInfo -> FC -> Env Term vars ->
          Value vars -> Value vars -> Core UnifyResult
  -- Deal with metavariable cases first
  -- If they're both holes, solve the one with the bigger context
  unifyNoEta mode fc env x@(VMeta fcx nx ix margsx argsx _) y@(VMeta fcy ny iy margsy argsy _)
      = do -- First check if they're convertible already, in which case
           -- we've won already
           False <- convert env x y
                | _ => pure success
           invx <- isDefInvertible fc ix
           if ix == iy && (invx || umode mode == InSearch)
                               -- Invertible, (from auto implicit search)
                               -- so we can also unify the arguments.
              then unifyArgs mode fc env
                             (map snd margsx ++ spineToValues argsx)
                             (map snd margsy ++ spineToValues argsy)
              else do xvs <- traverse expand (map snd margsx)
                      yvs <- traverse expand (map snd margsy)
                      let xlocs = localsIn xvs
                      let ylocs = localsIn yvs
                      -- Solve the one with the bigger context, and if they're
                      -- equal, the one that's applied to fewest things (because
                      -- then the arguments get substituted in)
                      let xbigger = xlocs > ylocs
                                      || (xlocs == ylocs &&
                                           length argsx <= length argsy)
                      if (xbigger || umode mode == InMatch) && not (pv nx)
                         then unifyHole False mode fc env fcx nx ix margsx argsx y
                         else unifyHole True mode fc env fcy ny iy margsy argsy x
    where
      pv : Name -> Bool
      pv (PV _ _) = True
      pv _ = False

      localsIn : List (Value vars) -> Nat
      localsIn [] = 0
      localsIn (VLocal{} :: xs) = 1 + localsIn xs
      localsIn (_ :: xs) = localsIn xs
  unifyNoEta mode fc env (VMeta fcm n i margs args _) tm
      = unifyHole False mode fc env fcm n i margs args tm
  unifyNoEta mode fc env tm (VMeta fcm n i margs args _)
      = unifyHole True mode fc env fcm n i margs args tm
  -- Unifying applications means we're stuck and need to postpone, since we've
  -- already checked convertibility
  -- In 'match' or 'search'  mode, we can nevertheless unify the arguments
  -- if the names match.
  unifyNoEta mode@(MkUnifyInfo p InSearch) fc env x@(VApp _ _ nx spx _) y@(VApp _ _ ny spy _)
      = if nx == ny
           then unifySpine mode fc env spx spy
           else postpone fc mode "Postponing application (search)" env x y
  unifyNoEta mode@(MkUnifyInfo p InMatch) fc env x@(VApp _ _ nx spx _) y@(VApp _ _ ny spy _)
      = if nx == ny
           then unifySpine mode fc env spx spy
           else postpone fc mode "Postponing application (match)" env x y
  unifyNoEta mode fc env x@(VApp{}) y
      = postpone fc mode "Postponing application (left)" env x y
  unifyNoEta mode fc env x y@(VApp{})
      = postpone fc mode "Postponing application (right)" env x y
  -- Now the cases where we're decomposing into smaller problems
  unifyNoEta mode fc env x@(VDCon fcx nx tx ax spx) y@(VDCon fcy ny ty ay spy)
      = if tx == ty
           then unifySpine mode fc env spx spy
           else convertError fc env x y
  unifyNoEta mode fc env x@(VTCon fcx nx ax spx) y@(VTCon fcy ny ay spy)
      = if nx == ny
           then unifySpine mode fc env spx spy
           else convertError fc env x y
  -- Something surprising has happened if we need to strip as patterns,
  -- but we'll include this for completeness.
  unifyNoEta mode fc env (VAs _ _ _ x) y = unifyNoEta mode fc env x y
  unifyNoEta mode fc env x (VAs _ _ _ y) = unifyNoEta mode fc env x y
  unifyNoEta mode fc env (VDelayed _ _ x) (VDelayed _ _ y)
      = unify (lower mode) fc env x y
  unifyNoEta mode fc env (VDelay _ _ tx ax) (VDelay _ _ ty ay)
      = unifyArgs (lower mode) fc env [tx,ax] [ty,ay]
  unifyNoEta mode fc env (VForce _ _ vx spx) (VForce _ _ vy spy)
      = do cs <- unify (lower mode) fc env vx vy
           cs' <- unifySpine (lower mode) fc env spx spy
           pure (union cs cs')
  unifyNoEta mode fc env x y
      = unifyIfEq (isDelay x || isDelay y) fc mode env x y
    where
      -- If one of them is a delay, and they're not equal, we'd better
      -- postpone and come back to it so we can insert the implicit
      -- Force/Delay later
      isDelay : Value vars -> Bool
      isDelay (VDelayed{}) = True
      isDelay _ = False

  mkArg : FC -> Name -> Value vars
  mkArg fc var = VApp fc Bound var [<] (pure Nothing)

  -- In practice, just Pi
  unifyBothBinders : {vars : _} ->
          UnifyInfo -> FC -> Env Term vars ->
          FC -> Name -> Binder (Value vars) -> (Value vars -> Core (Value vars)) ->
          FC -> Name -> Binder (Value vars) -> (Value vars -> Core (Value vars)) ->
          Core UnifyResult
  unifyBothBinders mode fc env fcx nx bx@(Pi bfcx cx ix tx) scx fcy ny by@(Pi bfcy cy iy ty) scy
      = if cx /= cy
          then convertError fc env
                 (VBind fcx nx bx scx)
                 (VBind fcy ny by scy)
          else do csarg <- unify (lower mode) fc env tx ty
                  tx' <- quote env tx
                  x' <- genVarName "x"
                  let env' : Env Term (_ :< nx)
                           = env :< Pi fcy cy Explicit tx'
                  case constraints csarg of
                      [] => -- No constraints, check the scope
                         do tscx <- scx (mkArg fc x')
                            tscy <- scy (mkArg fc x')
                            tmx <- quote env tscx
                            tmy <- quote env tscy
                            logTerm "unify.binder" 10 "Unifying scope" tmx
                            logTerm "unify.binder" 10 "..........with" tmy
                            unify (lower mode) fc env'
                              (refsToLocals (Add nx x' None) tmx)
                              (refsToLocals (Add nx x' None) tmy)
                      cs => -- Constraints, make new constant
                         do txtm <- quote env tx
                            tytm <- quote env ty
                            c <- newConstant fc erased env
                                   (Bind fcx nx (Lam fcy cy Explicit txtm) (Local fcx Nothing _ First))
                                   (Bind fcx nx (Pi fcy cy Explicit txtm)
                                       (weaken tytm)) cs
                            tscx <- scx (mkArg fc x')
                            tscy <- scy (mkArg fc x')
                            tmx <- quote env tscx
                            tmy <- quote env tscy
                            cs' <- unify (lower mode) fc env'
                                     (refsToLocals (Add nx x' None) tmx)
                                     (refsToLocals (Add nx x' None) tmy)
                            pure (union csarg cs')
  unifyBothBinders mode fc env fcx nx bx scx fcy ny by scy
      = convertError fc env
                  (VBind fcx nx bx scx)
                  (VBind fcy ny by scy)

  isHoleApp : Value vars -> Bool
  isHoleApp (VMeta{}) = True
  isHoleApp _ = False

  -- At this point, we know that 'VApp' and 'VMeta' don't reduce further
  unifyWithEta : {vars : _} ->
          UnifyInfo -> FC -> Env Term vars ->
          Value vars -> Value vars -> Core UnifyResult
  -- Pair of binders or lambdas
  unifyWithEta mode fc env (VBind fcx nx bx scx) (VBind fcy ny by scy)
      = unifyBothBinders mode fc env fcx nx bx scx fcy ny by scy
  unifyWithEta mode fc env x@(VLam fcx nx cx ix tx scx) y@(VLam fcy ny cy iy ty scy)
      = if cx /= cy
          then convertError fc env x y
          else do ct <- unify (lower mode) fc env tx ty
                  x' <- genVarName "x"
                  txtm <- quote env tx
                  let env' : Env Term (_ :< nx)
                           = env :< Lam fcx cx Explicit txtm
                  tscx <- scx (mkArg fc x')
                  tscy <- scy (mkArg fc x')
                  tmx <- quote env tscx
                  tmy <- quote env tscy
                  cs' <- unify (lower mode) fc env'
                               (refsToLocals (Add nx x' None) tmx)
                               (refsToLocals (Add nx x' None) tmy)
                  pure (union ct cs')
  -- Eta rules
  unifyWithEta mode fc env tmx@(VLam fcx x cx ix tx scx) tmy
        = do logNF "unify" 10 "EtaR" env tmx
             logNF "unify" 10 "...with" env tmy
             if isHoleApp tmy
                then if not !(convert env tmx tmy)
                        then unifyNoEta (lower mode) fc env tmx tmy
                        else pure success
                else do domty <- quote env tx
                        etay <- nf env
                                  $ Bind fcx x (Lam fcx cx Explicit domty)
                                  $ App fcx (weaken !(quote env tmy))
                                            cx
                                            (Local fcx Nothing 0 First)
                        logNF "unify" 10 "Expand" env etay
                        unify (lower mode) fc env tmx etay
  unifyWithEta mode fc env tmx tmy@(VLam fcy y cy iy ty scy)
        = do logNF "unify" 10 "EtaR" env tmx
             logNF "unify" 10 "...with" env tmy
             if isHoleApp tmy
                then if not !(convert env tmx tmy)
                        then unifyNoEta (lower mode) fc env tmx tmy
                        else pure success
                else do domty <- quote env ty
                        etax <- nf env
                                  $ Bind fcy y (Lam fcy cy Explicit domty)
                                  $ App fcy (weaken !(quote env tmx))
                                            cy
                                            (Local fcy Nothing 0 First)
                        logNF "unify" 10 "Expand" env etax
                        unify (lower mode) fc env etax tmy
  unifyWithEta mode fc env x y
      = unifyNoEta mode fc env x y

  -- At this point, we know that 'VApp' and 'VMeta' don't reduce further
  unifyLazy : {vars : _} ->
          UnifyInfo -> FC -> Env Term vars ->
          Value vars -> Value vars -> Core UnifyResult
  unifyLazy mode fc env (VDelayed _ _ x) (VDelayed _ _ y)
      = unifyWithEta (lower mode) fc env x y
  unifyLazy mode fc env x@(VDelayed _ r tmx) tmy
        -- TODO: why 'isHoleApp'
      = if isHoleApp tmy && not (umode mode == InMatch)
           then postpone fc mode "Postponing in lazy" env x tmy
           else do vs <- unify (lower mode) fc env tmx tmy
                   pure ({ addLazy := AddForce r } vs)
  unifyLazy mode fc env tmx (VDelayed _ r tmy)
      = do vs <- unify (lower mode) fc env tmx tmy
           pure ({ addLazy := AddDelay r } vs)
  unifyLazy mode fc env x y = unifyWithEta mode fc env x y

  -- First, see if we need to evaluate VApp a bit more
  -- Also, if we have two VApps that immediately convert without reduction,
  -- take advantage of that
  unifyExpandApps : {vars : _} ->
          Bool ->
          UnifyInfo -> FC -> Env Term vars ->
          Value vars -> Value vars -> Core UnifyResult
  -- If the values convert already, we're done
  unifyExpandApps lazy mode fc env x@(VApp fcx ntx nx spx valx) y@(VApp fcy nty ny spy valy)
      = if nx == ny
           then do c <- convertSpine fc env spx spy
                   if c
                      then pure success
                      else postpone fc mode "Postponing application"
                                    env x y
                           -- TODO: need to expand
           else do valx' <- expand x
                   valy' <- expand y
                   if lazy
                      then unifyLazy mode fc env valx' valy'
                      else unifyWithEta mode fc env valx' valy'
  -- Otherwise, make sure the top level thing is expanded (so not a reducible
  -- VApp or VMeta node) then move on
  unifyExpandApps lazy mode fc env x y
      = do x' <- expand x
           y' <- expand y
           if lazy
              then unifyLazy mode fc env x' y'
              else unifyWithEta mode fc env x' y'

  -- Start by expanding any top level Apps (if they don't convert already)
  -- then invoke full unification, either inserting laziness coercions
  -- or not.

  unifyVal : {vars : _} ->
          UnifyInfo -> FC -> Env Term vars ->
          Value vars -> Value vars -> Core UnifyResult
  unifyVal mode fc env x y = unifyExpandApps False mode fc env x y

  unifyValLazy : {vars : _} ->
          UnifyInfo -> FC -> Env Term vars ->
          Value vars -> Value vars -> Core UnifyResult
  unifyValLazy mode fc env x y = unifyExpandApps True mode fc env x y

  -- The interesting top level case, for unifying values
  Core.Unify.Unify.Value.unify mode fc env x y
     = unifyVal mode fc env x y

  -- The interesting top level case, for unifying values and inserting laziness
  -- coercions if appropriate
  Core.Unify.Unify.Value.unifyWithLazy mode fc env x y
     = unifyValLazy mode fc env x y

  Core.Unify.Unify.Term.unify umode fc env x y
     = do x' <- nf env x
          y' <- nf env y
          unify umode fc env x' y'

  Core.Unify.Unify.Term.unifyWithLazy umode fc env x y
     = do x' <- nf env x
          y' <- nf env y
          unifyWithLazy umode fc env x' y'

public export
data SolveMode = Normal -- during elaboration: unifies and searches
               | Defaults -- unifies and searches for default hints only
               | MatchArgs -- match rather than unify
               | LastChance -- as normal, but any failure throws rather than delays

Eq SolveMode where
  Normal == Normal = True
  Defaults == Defaults = True
  MatchArgs == MatchArgs = True
  LastChance == LastChance = True
  _ == _ = False

export
solveConstraints : {auto c : Ref Ctxt Defs} ->
                   {auto u : Ref UST UState} ->
                   UnifyInfo -> (smode : SolveMode) -> Core ()
