module Core.Unify.Unify

import Core.Core
import Core.Context
import Core.TT
import Core.Evaluate.Convert
import Core.Evaluate.Value

import Data.List

import Libraries.Data.IntMap

-- If we're unifying a Lazy type with a non-lazy type, we need to add an
-- explicit force or delay to the first argument to unification. This says
-- which to add, if any. Can only added at the very top level.
public export
data AddLazy = NoLazy | AddForce LazyReason | AddDelay LazyReason

public export
record UnifyResult where
  constructor MkUnifyResult
  constraints : List Int -- constraints generated, as index into UState IntMap
  holesSolved : Bool -- did we solve any holes?
  namesSolved : List Int -- which ones did we solve (as name indices)
  addLazy : AddLazy

union : UnifyResult -> UnifyResult -> UnifyResult
union u1 u2 = MkUnifyResult (union (constraints u1) (constraints u2))
                            (holesSolved u1 || holesSolved u2)
                            (namesSolved u1 ++ namesSolved u2)
                            NoLazy -- only top level, so assume no annotation

unionAll : List UnifyResult -> UnifyResult
unionAll [] = MkUnifyResult [] False [] NoLazy
unionAll [c] = c
unionAll (c :: cs) = union c (unionAll cs)

constrain : Int -> UnifyResult
constrain c = MkUnifyResult [c] False [] NoLazy

success : UnifyResult
success = MkUnifyResult [] False [] NoLazy

solvedHole : Int -> UnifyResult
solvedHole n = MkUnifyResult [] True [n] NoLazy

parameters {auto c : Ref Ctxt Defs}
  namespace Value
    export
    unify : {vars : _} ->
            FC -> Env Term vars -> Value vars -> Value vars -> Core UnifyResult

  namespace Term
    export
    unify : {vars : _} ->
            FC -> Env Term vars -> Term vars -> Term vars -> Core UnifyResult

  -- tmo catch all cases
  Core.Unify.Unify.Value.unify fc env x y
     = do chkConvert fc env x y
          pure success
  Core.Unify.Unify.Term.unify fc env x y
     = do chkConvert fc env x y
          pure success
