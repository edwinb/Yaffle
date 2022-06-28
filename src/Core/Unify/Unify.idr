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

parameters {auto c : Ref Ctxt Defs} {auto c : Ref UST UState}
  namespace Value
    export
    unify : {vars : _} ->
            UnifyInfo -> FC -> Env Term vars ->
            Value vars -> Value vars -> Core UnifyResult

  namespace Term
    export
    unify : {vars : _} ->
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

  -- tmp catch all cases
  Core.Unify.Unify.Value.unify umode fc env x y
     = do chkConvert fc env x y
          pure success

  Core.Unify.Unify.Term.unify umode fc env x y
     = do x' <- nf env x
          y' <- nf env y
          unify umode fc env x' y'
