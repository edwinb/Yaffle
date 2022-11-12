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
  -- Defined in Core.AutoSearch
  export
  search : {vars : _} ->
           FC -> RigCount ->
           (defaults : Bool) -> (depth : Nat) ->
           (defining : Name) -> (topTy : Term vars) -> Env Term vars ->
           Core (Term vars)

  namespace Value
    export
    unify : {vars : _} ->
            UnifyInfo -> FC -> Env Term vars ->
            Value f vars -> Value f' vars -> Core UnifyResult
    export
    unifyWithLazy : {vars : _} ->
            UnifyInfo -> FC -> Env Term vars ->
            Value f vars -> Value f' vars -> Core UnifyResult

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
            FC -> Env Term vars -> Value f vars -> Value f' vars -> Core a
  convertError loc env x y
      = do defs <- get Ctxt
           throw (CantConvert loc defs env !(quote env x) !(quote env y))

  convertGluedError : {vars : _} ->
            FC -> Env Term vars -> Glued vars -> Glued vars -> Core a
  convertGluedError loc env x y
      = do defs <- get Ctxt
           throw (CantConvert loc defs env !(quote env x) !(quote env y))

  convertErrorS : {vars : _} ->
            Bool -> FC -> Env Term vars -> Value f vars -> Value f' vars ->
            Core a
  convertErrorS s loc env x y
      = if s then convertError loc env y x
             else convertError loc env x y

  postpone : {vars : _} ->
             FC -> UnifyInfo -> String ->
             Env Term vars -> Value f vars -> Value f' vars -> Core UnifyResult
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
      checkDefined : Defs -> Value f vars -> Core ()
      checkDefined defs (VApp _ _ n _ _)
          = do Just _ <- lookupCtxtExact n (gamma defs)
                    | _ => undefinedName loc n
               pure ()
      checkDefined _ _ = pure ()

      undefinedN : Name -> Core Bool
      undefinedN n
          = do defs <- get Ctxt
               pure $ case !(lookupDefExact n (gamma defs)) of
                    Just (Hole _ _) => True
                    Just (BySearch _ _ _) => True
                    Just (Guess _ _ _) => True
                    _ => False

  postponeS : {vars : _} ->
              Bool -> FC -> UnifyInfo -> String -> Env Term vars ->
              Value f vars -> Value f' vars ->
              Core UnifyResult
  postponeS s loc mode logstr env x y
      = if s then postpone loc (lower mode) logstr env y x
             else postpone loc mode logstr env x y

  postponePatVar : {vars : _} ->
                   (swaporder : Bool) ->
                   UnifyInfo -> FC -> Env Term vars ->
                   (metaname : Name) -> (metaref : Int) ->
                   (margs : List (RigCount, Glued vars)) ->
                   (margs' : Spine vars) ->
                   (soln : Glued vars) ->
                   Core UnifyResult
  postponePatVar swap mode fc env mname mref margs margs' tm
      = do let x = VMeta fc mname mref margs margs' (pure Nothing)
           if !(convert env x tm)
              then pure success
              else postponeS {f=Normal}
                             swap fc mode "Not in pattern fragment" env
                             x tm

  unifyArgs : {vars : _} ->
              UnifyInfo -> FC -> Env Term vars ->
              List (Glued vars) -> List (Glued vars) ->
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
              FC -> UnifyInfo -> Env Term vars -> Glued vars -> Glued vars ->
              Core UnifyResult
  unifyIfEq post loc mode env x y
        = if !(convert env x y)
             then pure success
             else if post
                     then postpone loc mode ("Postponing unifyIfEq " ++
                                                 show (atTop mode)) env x y
                     else convertError loc env x y

  spineToValues : Spine vars -> List (Glued vars)
  spineToValues sp = toList (map third sp)

  headsConvert : {vars : _} ->
                 UnifyInfo ->
                 FC -> Env Term vars ->
                 Maybe (SnocList (Glued vars)) -> Maybe (SnocList (Glued vars)) ->
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
                (fnType : NF vars) -> SnocList (Glued vars) ->
                Core (Maybe (SnocList (Glued vars)))
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
                    (args : List (RigCount, Glued vars)) ->
                    (sp : Spine vars) ->
                    Maybe (Term [<]) ->
                    (Spine vars -> Glued vars) ->
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
                                 uargs <- unify {f=Normal} mode fc env
                                                (VMeta fc mname mref args hargs (pure Nothing))
                                                (con fargs)
                                 pure (union ures uargs)
                             else
                              do log "unify.invertible" 10 "Unifying invertible"
                                 ures <- unify mode fc env (third f) (third h)
                                 log "unify.invertible" 10 $ "Constraints " ++ show (constraints ures)
                                 uargs <- unify {f'=Normal} mode fc env
                                                (con fargs)
                                                (VMeta fc mname mref args hargs (pure Nothing))
                                 pure (union ures uargs))
                          (postponeS {f=Normal} swap fc mode "Postponing hole application [1]" env
                                (VMeta fc mname mref args sp (pure Nothing))
                                (con args'))
                     _ => postponeS {f=Normal} swap fc mode "Postponing hole application [2]" env
                                (VMeta fc mname mref args sp (pure Nothing))
                                (con args')
              else -- TODO: Cancellable function applications
                   postpone {f=Normal} fc mode "Postponing hole application [3]" env
                            (VMeta fc mname mref args sp (pure Nothing)) (con args')

  -- Unify a hole application - we have already checked that the hole is
  -- invertible (i.e. it's a determining argument to a proof search where
  -- it is a constructor or something else invertible in each case)
  unifyHoleApp : {vars : _} ->
                 (swaporder : Bool) ->
                 UnifyInfo -> FC -> Env Term vars ->
                 (metaname : Name) -> (metaref : Int) ->
                 (args : List (RigCount, Glued vars)) ->
                 (sp : Spine vars) ->
                 NF vars ->
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
              else postponeS {f=Normal} swap fc mode "Postponing hole application" env
                             (VMeta fc mname mref args sp (pure Nothing))
                             (asGlued tm)
    where
      isPatName : Name -> Bool
      isPatName (PV _ _) = True
      isPatName _ = False
  unifyHoleApp swap mode fc env mname mref args sp tm
      = postponeS {f=Normal} swap fc mode "Postponing hole application" env
                  (VMeta fc mname mref args sp (pure Nothing)) (asGlued tm)

  -- Solve a metavariable application (that is, the name applied the to
  -- args and spine) with the given solution.
  -- Also given the results we got from 'patternEnv' that tells us how to
  -- instantiate the environment in the solution
  solveHole : {newvars, vars : _} ->
              FC -> UnifyInfo -> Env Term vars ->
              (metaname : Name) -> (metaref : Int) ->
              (args : List (RigCount, Glued vars)) ->
              (sp : Spine vars) ->
              SnocList (Var newvars) ->
              SubVars newvars vars ->
              (solfull : Term vars) -> -- Original solution
              (soln : Term newvars) -> -- Solution with shrunk environment
              (solnf : Glued vars) ->
              Core (Maybe UnifyResult)
  solveHole fc mode env mname mref margs margs' locs submv solfull stm solnf
      = do defs <- get Ctxt
           ust <- get UST
           if solutionHeadSame !(expand solnf) || inNoSolve mref (noSolve ust)
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
      solutionHeadSame : NF vars -> Bool
      solutionHeadSame (VMeta _ _ shead _ _ _) = shead == mref
      solutionHeadSame _ = False

  -- Try to solve 'metaname' applied to all the arguments with the
  -- given solution
  unifyHole : {vars : _} ->
              (swaporder : Bool) ->
              UnifyInfo -> FC -> Env Term vars ->
              FC -> (metaname : Name) -> (metaref : Int) ->
              (args : List (RigCount, Glued vars)) ->
              (sp : Spine vars) ->
              (soln : Glued vars) ->
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
                     let Hole _ _ = definition hdef
                        | _ => postponePatVar swap mode fc env mname mref args sp tmnf
                     if invertible hdef
                        then unifyHoleApp swap mode fc env mname mref args sp !(expand tmnf)
                        else postponePatVar swap mode fc env mname mref args sp tmnf
                Just (newvars ** (locs, submv)) =>
                  do Just hdef <- lookupCtxtExact (Resolved mref) (gamma defs)
                         | _ => postponePatVar swap mode fc env mname mref args sp tmnf
                     let Hole _ _ = definition hdef
                         | _ => postponeS {f=Normal} swap fc mode "Delayed hole" env
                                          (VMeta fc mname mref args sp (pure Nothing))
                                          tmnf
                     tm <- quote env tmnf
                     Just tm <- occursCheck fc env mode mname tm
                         | _ => postponeS {f=Normal} swap fc mode "Occurs check failed" env
                                          (VMeta fc mname mref args sp (pure Nothing))
                                          tmnf
                     let solveOrElsePostpone : Term newvars -> Core UnifyResult
                         solveOrElsePostpone stm = do
                           mbResult <- solveHole fc mode env mname mref
                                            args sp locs submv
                                            tm stm tmnf
                           flip fromMaybe (pure <$> mbResult) $
                             postponeS {f=Normal} swap fc mode "Can't instantiate" env
                                       (VMeta fc mname mref args sp (pure Nothing))
                                       tmnf
                     case shrinkTerm tm submv of
                          Just stm => solveOrElsePostpone stm
                          Nothing =>
                            do tm' <- quote env tmnf
                               case shrinkTerm tm' submv of
                                    Nothing => postponeS {f=Normal} swap fc mode "Can't shrink" env
                                                 (VMeta fc mname mref args sp (pure Nothing))
                                                 tmnf
                                    Just stm => solveOrElsePostpone stm

  -- Main bit of unification, decomposing unification problems into
  -- sub-problems and solving metavariables where appropriate
  unifyNoEta : {vars : _} ->
          UnifyInfo -> FC -> Env Term vars ->
          Value f vars -> Value f' vars -> Core UnifyResult
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
                         then unifyHole False mode fc env fcx nx ix margsx argsx (asGlued y)
                         else unifyHole True mode fc env fcy ny iy margsy argsy (asGlued x)
    where
      pv : Name -> Bool
      pv (PV _ _) = True
      pv _ = False

      localsIn : List (NF vars) -> Nat
      localsIn [] = 0
      localsIn (VLocal{} :: xs) = 1 + localsIn xs
      localsIn (_ :: xs) = localsIn xs
  unifyNoEta mode fc env (VMeta fcm n i margs args _) tm
      = unifyHole False mode fc env fcm n i margs args (asGlued tm)
  unifyNoEta mode fc env tm (VMeta fcm n i margs args _)
      = unifyHole True mode fc env fcm n i margs args (asGlued tm)
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
  unifyNoEta mode fc env x_in y_in
      = do x <- expand x_in
           y <- expand y_in
           unifyIfEq (isDelay x || isDelay y) fc mode env (asGlued x) (asGlued y)
    where
      -- If one of them is a delay, and they're not equal, we'd better
      -- postpone and come back to it so we can insert the implicit
      -- Force/Delay later
      isDelay : NF vars -> Bool
      isDelay (VDelayed{}) = True
      isDelay _ = False

  mkArg : FC -> Name -> Glued vars
  mkArg fc var = VApp fc Bound var [<] (pure Nothing)

  -- In practice, just Pi
  unifyBothBinders : {vars : _} ->
          UnifyInfo -> FC -> Env Term vars ->
          FC -> Name -> Binder (Glued vars) -> (Glued vars -> Core (Glued vars)) ->
          FC -> Name -> Binder (Glued vars) -> (Glued vars -> Core (Glued vars)) ->
          Core UnifyResult
  unifyBothBinders mode fc env fcx nx bx@(Pi bfcx cx ix tx) scx fcy ny by@(Pi bfcy cy iy ty) scy
      = if cx /= cy
          then convertGluedError fc env
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
      = convertGluedError fc env
                  (VBind fcx nx bx scx)
                  (VBind fcy ny by scy)

  isHoleApp : NF vars -> Bool
  isHoleApp (VMeta{}) = True
  isHoleApp _ = False

  -- At this point, we know that 'VApp' and 'VMeta' don't reduce further
  unifyWithEta : {vars : _} ->
          UnifyInfo -> FC -> Env Term vars ->
          NF vars -> NF vars -> Core UnifyResult
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
          NF vars -> NF vars -> Core UnifyResult
  unifyLazy mode fc env (VDelayed _ _ x) (VDelayed _ _ y)
      = unifyWithEta (lower mode) fc env !(expand x) !(expand y)
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
          Glued vars -> Glued vars -> Core UnifyResult
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
          Glued vars -> Glued vars -> Core UnifyResult
  unifyVal mode fc env x y = unifyExpandApps False mode fc env x y

  unifyValLazy : {vars : _} ->
          UnifyInfo -> FC -> Env Term vars ->
          Glued vars -> Glued vars -> Core UnifyResult
  unifyValLazy mode fc env x y = unifyExpandApps True mode fc env x y

  -- The interesting top level case, for unifying values
  Core.Unify.Unify.Value.unify mode fc env x y
     = unifyVal mode fc env (asGlued x) (asGlued y)

  -- The interesting top level case, for unifying values and inserting laziness
  -- coercions if appropriate
  Core.Unify.Unify.Value.unifyWithLazy mode fc env x y
     = unifyValLazy mode fc env (asGlued x) (asGlued y)

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

parameters {auto c : Ref Ctxt Defs} {auto c : Ref UST UState}
  retry : UnifyInfo -> Int -> Core UnifyResult
  retry mode c
      = do ust <- get UST
           case lookup c (constraints ust) of
                Nothing => pure success
                Just Resolved => pure success
                Just (MkConstraint loc withLazy env xold yold)
                 => do defs <- get Ctxt
                       x <- nf env xold
                       y <- nf env yold
                       catch
                         (do cs <- ifThenElse withLazy
                                      (unifyWithLazy mode loc env x y)
                                      (unify (lower mode) loc env x y)
                             case constraints cs of
                               [] => do deleteConstraint c
                                        pure cs
                               _ => pure cs)
                        (\err => do defs <- get Ctxt
                                    throw (WhenUnifying loc defs env
                                                        !(quote env x)
                                                        !(quote env y) err))
                Just (MkSeqConstraint loc env xsold ysold)
                    => do defs <- get Ctxt
                          xs <- traverse (nf env) xsold
                          ys <- traverse (nf env) ysold
                          cs <- unifyArgs mode loc env xs ys
                          case constraints cs of
                               [] => do deleteConstraint c
                                        pure cs
                               _ => pure cs
    where
      definedN : Name -> Core Bool
      definedN n@(NS _ (MN _ _)) -- a metavar will only ever be a MN
          = do defs <- get Ctxt
               Just gdef <- lookupCtxtExact n (gamma defs)
                    | _ => pure False
               case definition gdef of
                    Hole _ _ => pure (invertible gdef)
                    BySearch _ _ _ => pure False
                    Guess _ _ _ => pure False
                    _ => pure True
      definedN _ = pure True

  delayMeta : {vars : _} ->
              LazyReason -> Nat -> Term vars -> Term vars -> Term vars
  delayMeta r (S k) ty (Bind fc n b sc)
      = Bind fc n b (delayMeta r k (weaken ty) sc)
  delayMeta r envb ty tm = TDelay (getLoc tm) r ty tm

  forceMeta : LazyReason -> Nat -> Term vars -> Term vars
  forceMeta r (S k) (Bind fc n b sc)
      = Bind fc n b (forceMeta r k sc)
  forceMeta r envb tm = TForce (getLoc tm) r tm

  -- Check whether it's worth trying a search again, based on what went wrong
  recoverable : Error -> Bool
  recoverable (UndefinedName _ _) = False
  recoverable (InType _ _ err) = recoverable err
  recoverable (InCon _ _ err) = recoverable err
  recoverable (InLHS _ _ err) = recoverable err
  recoverable (InRHS _ _ err) = recoverable err
  recoverable (WhenUnifying _ _ _ _ _ err) = recoverable err
  recoverable (MaybeMisspelling err _) = recoverable err
  recoverable _ = True

  -- Retry the given constraint, return True if progress was made
  retryGuess : UnifyInfo -> (smode : SolveMode) -> (hole : (Int, (FC, Name))) ->
               Core Bool
  retryGuess mode smode (hid, (loc, hname))
      = do defs <- get Ctxt
           case !(lookupCtxtExact (Resolved hid) (gamma defs)) of
             Nothing => pure False
             Just def =>
               case definition def of
                 BySearch rig depth defining =>
                    handleUnify
                       (do tm <- search loc rig (smode == Defaults) depth defining
                                        (type def) [<]
                           let gdef = { definition := Function defaultFI tm } def
                           ignore $ addDef (Resolved hid) gdef
                           removeGuess hid
                           pure True)
                       $ \case
                         DeterminingArg _ n i _ _ =>
                           do logTerm "unify.retry" 5
                                      ("Failed (det " ++ show hname ++ " " ++ show n ++ ")")
                                      (type def)
                              setInvertible loc (Resolved i)
                              pure False -- progress not made yet!
                         err =>
                           case smode of
                                LastChance => throw err
                                _ => if recoverable err
                                        then pure False -- Postpone again
                                        else throw (CantSolveGoal loc defs
                                                       [<] (type def) (Just err))
                 -- TODO: Check if this is still needed as a performance
                 -- hack
                 Guess tm envb [constr] =>
                   do let umode = case smode of
                                       MatchArgs => inMatch
                                       _ => mode
                      cs <- retry umode constr
                      case constraints cs of
                           [] => do tm' <- case addLazy cs of
                                             NoLazy => pure tm
                                             AddForce r => pure $ forceMeta r envb tm
                                             AddDelay r =>
                                                do logTerm "unify.retry" 5 "Retry Delay" tm
                                                   pure $ delayMeta r envb (type def) tm
                                    let gdef = { definition := Function (MkFnInfo NotHole True False) tm' } def
                                    logTerm "unify.retry" 5 ("Resolved " ++ show hname) tm'
                                    ignore $ addDef (Resolved hid) gdef
                                    removeGuess hid
                                    pure (holesSolved cs)
                           newcs => do tm' <- case addLazy cs of
                                             NoLazy => pure tm
                                             AddForce r => pure $ forceMeta r envb tm
                                             AddDelay r =>
                                                do logTerm "unify.retry" 5 "Retry Delay (constrained)" tm
                                                   pure $ delayMeta r envb (type def) tm
                                       let gdef = { definition := Guess tm' envb newcs } def
                                       ignore $ addDef (Resolved hid) gdef
                                       pure False
                 Guess tm envb constrs =>
                   do let umode = case smode of
                                       MatchArgs => inMatch
                                       _ => mode
                      cs' <- traverse (retry umode) constrs
                      let csAll = unionAll cs'
                      case constraints csAll of
                           -- All constraints resolved, so turn into a
                           -- proper definition and remove it from the
                           -- hole list
                           [] => do let gdef = { definition := Function (MkFnInfo NotHole True False) tm } def
                                    logTerm "unify.retry" 5 ("Resolved " ++ show hname) tm
                                    ignore $ addDef (Resolved hid) gdef
                                    removeGuess hid
                                    pure (holesSolved csAll)
                           newcs => do let gdef = { definition := Guess tm envb newcs } def
                                       ignore $ addDef (Resolved hid) gdef
                                       pure False
                 _ => pure False

  export
  solveConstraints : UnifyInfo -> (smode : SolveMode) -> Core ()
  solveConstraints umode smode
      = do ust <- get UST
           progress <- traverse (retryGuess umode smode) (toList (guesses ust))
           when (any id progress) $
                 solveConstraints umode Normal

  export
  solveConstraintsAfter : Int -> UnifyInfo -> (smode : SolveMode) -> Core ()
  solveConstraintsAfter start umode smode
      = do ust <- get UST
           progress <- traverse (retryGuess umode smode)
                                (filter afterStart (toList (guesses ust)))
           when (any id progress) $
                 solveConstraintsAfter start umode Normal
    where
      afterStart : (Int, a) -> Bool
      afterStart (x, _) = x >= start

  -- Replace any 'BySearch' with 'Hole', so that we don't keep searching
  -- fruitlessly while elaborating the rest of a source file
  export
  giveUpConstraints : Core ()
  giveUpConstraints
      = do ust <- get UST
           traverse_ constraintToHole (toList (guesses ust))
    where
      constraintToHole : (Int, (FC, Name)) -> Core ()
      constraintToHole (hid, (_, _))
          = do defs <- get Ctxt
               case !(lookupDefExact (Resolved hid) (gamma defs)) of
                    Just (BySearch _ _ _) =>
                           updateDef (Resolved hid) (const (Just (Hole 0 (holeInit False))))
                    Just (Guess _ _ _) =>
                           updateDef (Resolved hid) (const (Just (Hole 0 (holeInit False))))
                    _ => pure ()

  -- Check whether any of the given hole references have the same solution
  -- (up to conversion)
  export
  checkArgsSame : List Int -> Core Bool
  checkArgsSame [] = pure False
  checkArgsSame (x :: xs)
      = do defs <- get Ctxt
           Just (Function _ def) <-
                      lookupDefExact (Resolved x) (gamma defs)
                | _ => checkArgsSame xs
           s <- anySame def xs
           if s
              then pure True
              else checkArgsSame xs
    where
      anySame : ClosedTerm -> List Int -> Core Bool
      anySame tm [] = pure False
      anySame tm (t :: ts)
          = do defs <- get Ctxt
               Just (Function _ def) <-
                          lookupDefExact (Resolved t) (gamma defs)
                   | _ => anySame tm ts
               if !(convert [<] tm def)
                  then pure True
                  else anySame tm ts

  export
  checkDots : Core ()
  checkDots
      = do ust <- get UST
           hs <- getCurrentHoles
           traverse_ checkConstraint (reverse (dotConstraints ust))
           hs <- getCurrentHoles
           update UST { dotConstraints := [] }
    where
      getHoleName : Term [<] -> Core (Maybe Name)
      getHoleName tm
          = do defs <- get Ctxt
               VMeta _ n' i _ _ _ <- expand !(nf [<] tm)
                   | _ => pure Nothing
               pure (Just n')

      checkConstraint : (Name, DotReason, Constraint) -> Core ()
      checkConstraint (n, reason, MkConstraint fc wl env xold yold)
          = do defs <- get Ctxt
               x <- nf env xold
               y <- nf env yold
               -- A dot is okay if the constraint is solvable *without solving
               -- any additional holes*
               ust <- get UST
               handleUnify
                 (do defs <- get Ctxt
                     -- get the hole name that 'n' is currently resolved to,
                     -- if indeed it is still a hole
                     (i, _) <- getPosition n (gamma defs)
                     oldholen <- getHoleName (Meta fc n i [])
                     -- Check that what was given (x) matches what was
                     -- solved by unification (y).
                     -- In 'InMatch' mode, only metavariables in 'x' can
                     -- be solved, so everything in the dotted metavariable
                     -- must be complete.
                     cs <- unify inMatch fc env x y
                     defs <- get Ctxt
                     -- If the name standing for the dot wasn't solved
                     -- earlier, but is now (even with another metavariable)
                     -- this is bad (it most likely means there's a non-linear
                     -- variable)
                     dotSolved <-
                        maybe (pure False)
                              (\n => do Just ndef <- lookupDefExact n (gamma defs)
                                             | Nothing => undefinedName fc n
                                        pure $ case ndef of
                                             Hole _ _ => False
                                             _ => True)
                              oldholen

                     -- If any of the things we solved have the same definition,
                     -- we've sneaked a non-linear pattern variable in
                     argsSame <- checkArgsSame (namesSolved cs)
                     when (not (isNil (constraints cs))
                              || dotSolved || argsSame) $
                        throw (InternalError "Dot pattern match fail"))
                 (\err =>
                      case err of
                           InternalError _ =>
                             do defs <- get Ctxt
                                Just dty <- lookupTyExact n (gamma defs)
                                     | Nothing => undefinedName fc n
                                logTermNF "unify.constraint" 5 "Dot type" [<] dty
                                -- Clear constraints so we don't report again
                                -- later
                                put UST ({ dotConstraints := [] } ust)
                                throw (BadDotPattern fc env reason
                                        !(quote env x)
                                        !(quote env y))
                           _ => do put UST ({ dotConstraints := [] } ust)
                                   throw err)
      checkConstraint _ = pure ()
