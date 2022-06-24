module Core.Unify.Unify

import Core.Core
import Core.Context
import Core.TT
import Core.Evaluate

import Data.List

import Libraries.Data.IntMap

public export
data UnifyMode = InLHS
               | InTerm
               | InMatch
               | InSearch

-- Need to record if we're at the top level or not, because top level things
-- can have Force and Delay inserted, and may have been postponed.
public export
record UnifyInfo where
  constructor MkUnifyInfo
  atTop : Bool
  umode : UnifyMode

export
inTerm : UnifyInfo
inTerm = MkUnifyInfo True InTerm

export
inLHS : UnifyInfo
inLHS = MkUnifyInfo True InLHS

export
inMatch : UnifyInfo
inMatch = MkUnifyInfo True InMatch

export
inSearch : UnifyInfo
inSearch = MkUnifyInfo True InSearch

lower : UnifyInfo -> UnifyInfo
lower = { atTop := False }

Eq UnifyMode where
   InLHS == InLHS = True
   InTerm == InTerm = True
   InMatch == InMatch = True
   InSearch == InSearch = True
   _ == _ = False

Eq UnifyInfo where
  x == y = atTop x == atTop y && umode x == umode y

Show UnifyMode where
  show InLHS = "InLHS"
  show InTerm = "InTerm"
  show InMatch = "InMatch"
  show InSearch = "InSearch"

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

ufail : FC -> String -> Core a
ufail loc msg = throw (GenericMsg loc msg)



parameters {auto c : Ref Ctxt Defs}
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


  -- tmp catch all cases
  Core.Unify.Unify.Value.unify umode fc env x y
     = do chkConvert fc env x y
          pure success

  Core.Unify.Unify.Term.unify umode fc env x y
     = do x' <- nf env x
          y' <- nf env y
          unify umode fc env x' y'
