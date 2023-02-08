module TTImp.Elab.Delayed

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.Metadata
import Core.Evaluate
import Core.Unify
import Core.TT

import TTImp.Elab.Check

import Libraries.Data.IntMap
import Libraries.Data.NameMap
import Data.List
import Data.SnocList

%default covering

-- We run the elaborator in the given environment, but need to end up with a
-- closed term.
mkClosedElab : {vars : _} ->
               FC -> Env Term vars ->
               (Core (Term vars, Glued vars)) ->
               Core ClosedTerm
mkClosedElab fc [<] elab
    = do (tm, _) <- elab
         pure tm
mkClosedElab {vars = vars :< x} fc (env :< b) elab
    = mkClosedElab fc env
          (do (sc', _) <- elab
              let b' = newBinder b
              pure (Bind fc x b' sc', VErased fc Placeholder))
  where
    -- in 'abstractEnvType' we get a Pi binder (so we'll need a Lambda) for
    -- everything except 'Let', so make the appropriate corresponding binder
    -- here
    newBinder : Binder (Term vars) -> Binder (Term vars)
    newBinder b@(Let _ _ _ _) = b
    newBinder b = Lam (binderLoc b) (multiplicity b) Explicit (binderType b)

deeper : {auto e : Ref EST (EState vars)} ->
         Core a -> Core a
deeper elab
    = do est <- get EST
         let d = delayDepth est
         put EST ({ delayDepth := 1 + d } est)
         res <- elab
         est <- get EST
         put EST ({ delayDepth := d } est)
         pure res

-- Try the given elaborator; if it fails, and the error matches the
-- predicate, make a hole and try it again later when more holes might
-- have been resolved
export
delayOnFailure : {vars : _} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto m : Ref MD Metadata} ->
                 {auto u : Ref UST UState} ->
                 {auto e : Ref EST (EState vars)} ->
                 FC -> RigCount -> ElabInfo -> Env Term vars ->
                 (expected : Maybe (Glued vars)) ->
                 (Error -> Bool) ->
                 (pri : DelayReason) ->
                 (Bool -> Core (Term vars, Glued vars)) ->
                 Core (Term vars, Glued vars)
delayOnFailure fc rig elabinfo env exp pred pri elab
    = do ust <- get UST
         let nos = noSolve ust -- remember the holes we shouldn't solve
         handle (elab False)
          (\err =>
              do est <- get EST
                 expected <- mkExpected exp
                 if pred err
                    then
                      do nm <- genName "delayed"
                         (ci, dtm) <- newDelayed fc linear env nm !(quote env expected)
                         defs <- get Ctxt
                         update UST { delayedElab $=
                             ((pri, ci, localHints defs,
                               mkClosedElab fc env
                                  (deeper
                                    (do ust <- get UST
                                        let nos' = noSolve ust
                                        put UST ({ noSolve := nos } ust)
                                        (restm, resty) <- elab True
                                        ust <- get UST
                                        put UST ({ noSolve := nos' } ust)
                                        checkExp rig elabinfo env fc restm resty (Just expected)
                                        ))) :: ) }
                         pure (dtm, expected)
                    else throw err)
  where
    mkExpected : Maybe (Glued vars) -> Core (Glued vars)
    mkExpected (Just ty) = pure ty
    mkExpected Nothing
        = do nm <- genName "delayTy"
             u <- uniVar fc
             ty <- metaVar fc erased env nm (TType fc u)
             nf env ty

export
delayElab : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto m : Ref MD Metadata} ->
            {auto u : Ref UST UState} ->
            {auto e : Ref EST (EState vars)} ->
            FC -> RigCount -> ElabInfo -> Env Term vars ->
            (expected : Maybe (Glued vars)) ->
            (pri : DelayReason) ->
            Core (Term vars, Glued vars) ->
            Core (Term vars, Glued vars)
delayElab {vars} fc rig elabinfo env exp pri elab
    = do ust <- get UST
         let nos = noSolve ust -- remember the holes we shouldn't solve
         nm <- genName "delayed"
         expected <- mkExpected exp
         (ci, dtm) <- newDelayed fc linear env nm !(quote env expected)
         defs <- get Ctxt
         update UST { delayedElab $=
                 ((pri, ci, localHints defs, mkClosedElab fc env
                              (do ust <- get UST
                                  let nos' = noSolve ust
                                  put UST ({ noSolve := nos } ust)
                                  (restm, resty) <- elab
                                  ust <- get UST
                                  put UST ({ noSolve := nos' } ust)
                                  checkExp rig elabinfo env fc restm resty (Just expected)
                                  )) :: ) }
         pure (dtm, expected)
  where
    mkExpected : Maybe (Glued vars) -> Core (Glued vars)
    mkExpected (Just ty) = pure ty
    mkExpected Nothing
        = do nm <- genName "delayTy"
             u <- uniVar fc
             ty <- metaVar fc erased env nm (TType fc u)
             nf env ty

export
ambiguous : Error -> Bool
ambiguous (AmbiguousElab _ _ _) = True
ambiguous (AmbiguousName _ _) = True
ambiguous (AmbiguityTooDeep _ _ _) = True
ambiguous (InType _ _ err) = ambiguous err
ambiguous (InCon _ _ err) = ambiguous err
ambiguous (InLHS _ _ err) = ambiguous err
ambiguous (InRHS _ _ err) = ambiguous err
ambiguous (WhenUnifying _ _ _ _ _ err) = ambiguous err
ambiguous _ = False

zipArgs : {auto c : Ref Ctxt Defs} ->
          Spine vars -> Spine vars -> Core (List (NF vars, NF vars))
zipArgs [<] _ = pure []
zipArgs _ [<] = pure []
zipArgs (as :< a) (bs :< b)
   = do sp <- zipArgs as bs
        pure $ (!(spineVal a), !(spineVal b)) :: sp

mutual
  mismatchNF : {auto c : Ref Ctxt Defs} ->
               {vars : _} ->
               NF vars -> NF vars -> Core Bool
  mismatchNF (VTCon _ xn _ xargs) (VTCon _ yn _ yargs)
      = if xn /= yn
           then pure True
           else anyM mismatch !(zipArgs xargs yargs)
  mismatchNF (VDCon _ _ xt _ xargs) (VDCon _ _ yt _ yargs)
      = if xt /= yt
           then pure True
           else anyM mismatch !(zipArgs xargs yargs)
  mismatchNF (VPrimVal _ xc) (VPrimVal _ yc) = pure (xc /= yc)
  mismatchNF (VDelayed _ _ x) (VDelayed _ _ y)
      = mismatchNF !(expand x) !(expand y)
  mismatchNF (VDelay _ _ _ x) (VDelay _ _ _ y)
      = mismatchNF !(expand x) !(expand y)
  mismatchNF _ _ = pure False

  mismatch : {auto c : Ref Ctxt Defs} ->
             {vars : _} ->
             (NF vars, NF vars) -> Core Bool
  mismatch (x, y) = mismatchNF x y

contra : {auto c : Ref Ctxt Defs} ->
         {vars : _} ->
         NF vars -> NF vars -> Core Bool
-- Unlike 'impossibleOK', any mismatch indicates an unrecoverable error
contra (VTCon _ xn xa xargs) (VTCon _ yn ya yargs)
    = if xn /= yn
         then pure True
         else anyM mismatch !(zipArgs xargs yargs)
contra (VDCon _ _ xt _ xargs) (VDCon _ _ yt _ yargs)
    = if xt /= yt
         then pure True
         else anyM mismatch !(zipArgs xargs yargs)
contra (VPrimVal _ x) (VPrimVal _ y) = pure (x /= y)
contra (VDCon _ _ _ _ _) (VPrimVal _ _) = pure True
contra (VPrimVal _ _) (VDCon _ _ _ _ _) = pure True
contra x y = pure False

-- Errors that might be recoverable later if we try again. Generally -
-- ambiguity errors, type inference errors
export
recoverable : {auto c : Ref Ctxt Defs} ->
              Error -> Core Bool
recoverable (CantConvert _ defs' env l r)
   = do defs <- get Ctxt
        put Ctxt defs'
        let res = not !(contra !(expand !(nf env l)) !(expand !(nf env r)))
        put Ctxt defs
        pure res
recoverable (CantSolveEq _ defs' env l r)
   = do defs <- get Ctxt
        put Ctxt defs'
        let res = not !(contra !(expand !(nf env l)) !(expand !(nf env r)))
        put Ctxt defs
        pure res
recoverable (UndefinedName _ _) = pure False
recoverable (LinearMisuse _ _ _ _) = pure False
recoverable (InType _ _ err) = recoverable err
recoverable (InCon _ _ err) = recoverable err
recoverable (InLHS _ _ err) = recoverable err
recoverable (InRHS _ _ err) = recoverable err
recoverable (WhenUnifying _ _ _ _ _ err) = recoverable err
recoverable _ = pure True

data RetryError
     = RecoverableErrors
     | AllErrors

Show RetryError where
  show RecoverableErrors = "RecoverableErrors"
  show AllErrors = "AllErrors"

-- Try all the delayed elaborators. If there's a failure, we want to
-- show the ambiguity errors first (since that's the likely cause)
-- Return all the ones that need trying again
retryDelayed' : {vars : _} ->
                {auto c : Ref Ctxt Defs} ->
                {auto m : Ref MD Metadata} ->
                {auto u : Ref UST UState} ->
                {auto e : Ref EST (EState vars)} ->
                RetryError ->
                (progress : Bool) ->
                List (DelayReason, Int, NameMap (), Core ClosedTerm) ->
                List (DelayReason, Int, NameMap (), Core ClosedTerm) ->
                Core (Bool, List (DelayReason, Int, NameMap (), Core ClosedTerm))
retryDelayed' errmode p acc [] = pure (p, reverse acc)
retryDelayed' errmode p acc (d@(_, i, hints, elab) :: ds)
    = do defs <- get Ctxt
         Just Delayed <- lookupDefExact (Resolved i) (gamma defs)
              | _ => retryDelayed' errmode p acc ds
         handle
           (do est <- get EST
               log "elab.retry" 5 (show (delayDepth est) ++ ": Retrying delayed hole " ++ show !(getFullName (Resolved i)))
               -- elab itself might have delays internally, so keep track of them
               update UST { delayedElab := [] }
               update Ctxt { localHints := hints }

               tm <- elab
               ust <- get UST
               let ds' = reverse (delayedElab ust) ++ ds

               updateDef (Resolved i) (const (Just
                    (Function (MkFnInfo NotHole True False) tm tm Nothing)))
               logTerm "elab.update" 5 ("Resolved delayed hole " ++ show i) tm
               logTermNF "elab.update" 5 ("Resolved delayed hole NF " ++ show i) [<] tm
               removeHole i
               retryDelayed' errmode True acc ds')
           (\err => do log "elab" 5 $ show errmode ++ ":Error in " ++ show !(getFullName (Resolved i))
                                ++ "\n" ++ show err
                       case errmode of
                         RecoverableErrors =>
                            if not !(recoverable err)
                               then throw err
                               else retryDelayed' errmode p (d :: acc) ds
                         AllErrors =>
                            -- we've got an error, but see if we get a more
                            -- helpful one with a later elaborator
                            handle (do ignore $ retryDelayed' errmode p [] ds
                                       throw err)
                               (\err' => throw (better err err')))
  where
    better : Error -> Error -> Error
    better e (GenericMsg _ _) = e
    better (GenericMsg _ _) e = e
    better e _ = e

export
retryDelayed : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               {auto m : Ref MD Metadata} ->
               {auto u : Ref UST UState} ->
               {auto e : Ref EST (EState vars)} ->
               UnifyInfo -> List (DelayReason, Int, NameMap (), Core ClosedTerm) ->
               Core ()
retryDelayed mode ds
    = do (p, ds) <- retryDelayed' RecoverableErrors False [] ds -- try everything again
         solveConstraints mode Normal -- maybe we can resolve some interfaces now
         if p
            then retryDelayed mode ds -- progress, go around again
            else ignore $ retryDelayed' AllErrors False [] ds -- fail on all errors

-- Run an elaborator, then all the delayed elaborators arising from it
export
runDelays : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto m : Ref MD Metadata} ->
            {auto u : Ref UST UState} ->
            {auto e : Ref EST (EState vars)} ->
            (DelayReason -> Bool) -> Core a -> Core a
runDelays pri elab
    = do ust <- get UST
         let olddelayed = delayedElab ust
         put UST ({ delayedElab := [] } ust)
         tm <- elab
         ust <- get UST
         log "elab.delay" 2 $ "Rerunning delayed in elaborator"
         handle (do ignore $ retryDelayed' AllErrors False []
                       (reverse (filter hasPri (delayedElab ust))))
                (\err => do put UST ({ delayedElab := olddelayed } ust)
                            throw err)
         update UST { delayedElab $= (++ olddelayed) }
         pure tm
  where
    hasPri : (DelayReason, d) -> Bool
    hasPri (n, _) = pri n
