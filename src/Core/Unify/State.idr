module Core.Unify.State

import Core.Context
import Core.Context.Log
import Core.Env
import Core.Error
import Core.TT

import Data.SnocList

import Libraries.Data.IntMap

public export
data Constraint : Type where
     -- An unsolved constraint, noting two terms which need to be convertible
     -- in a particular environment
     MkConstraint : {vars : _} ->
                    FC ->
                    (withLazy : Bool) ->
                    (env : Env Term vars) ->
                    (x : Term vars) -> (y : Term vars) ->
                    Constraint
     -- An unsolved sequence of constraints, arising from arguments in an
     -- application where solving later constraints relies on solving earlier
     -- ones
     MkSeqConstraint : {vars : _} ->
                       FC ->
                       (env : Env Term vars) ->
                       (xs : List (Term vars)) ->
                       (ys : List (Term vars)) ->
                       Constraint
     -- A resolved constraint
     Resolved : Constraint

-- a constraint on the LHS arising from checking an argument in a position
-- where we expect a polymorphic type. If, in the end, the expected type is
-- polymorphic but the argument is concrete, then the pattern match is too
-- specific
public export
data PolyConstraint : Type where
     MkPolyConstraint : {vars : _} ->
                        FC -> Env Term vars ->
                        (arg : Term vars) ->
                        (expty : Term vars) ->
                        (argty : Term vars) -> PolyConstraint

public export
record UState where
  constructor MkUState
  holes : IntMap (FC, Name) -- All metavariables with no definition yet.
                            -- 'Int' is the 'Resolved' name
  guesses : IntMap (FC, Name) -- Names which will be defined when constraints solved
                              -- (also includes auto implicit searches)
  currentHoles : IntMap (FC, Name) -- Holes introduced this elaboration session
  delayedHoles : IntMap (FC, Name) -- Holes left unsolved after an elaboration,
                                   -- so we need to check again at the end whether
                                   -- they have been solved later. Doesn't include
                                   -- user defined hole names, which don't need
                                   -- to have been solved
  constraints : IntMap Constraint -- map for finding constraints by ID
  noSolve : IntMap () -- Names not to solve
                      -- If we're checking an LHS, then checking an argument can't
                      -- solve its own type, or we might end up with something
                      -- less polymorphic than it should be
  polyConstraints : List PolyConstraint -- constraints which need to be solved
                      -- successfully to check an LHS is polymorphic enough
  dotConstraints : List (Name, DotReason, Constraint) -- dot pattern constraints
  nextName : Int
  nextConstraint : Int
--   delayedElab : List (DelayReason, Int, NameMap (), Core ClosedTerm)
--                 -- Elaborators which we need to try again later, because
--                 -- we didn't have enough type information to elaborate
--                 -- successfully yet.
--                 -- The 'Int' is the resolved name.
--                 -- NameMap () is the set of local hints at the point of delay
  logging : Bool

export
initUState : UState
initUState = MkUState
  { holes = empty
  , guesses = empty
  , currentHoles = empty
  , delayedHoles = empty
  , constraints = empty
  , noSolve = empty
  , polyConstraints = []
  , dotConstraints = []
  , nextName = 0
  , nextConstraint = 0
--   , delayedElab = []
  , logging = False
  }

export
data UST : Type where

mkConstantAppArgs : {vars : _} ->
                    Bool -> FC -> Env Term vars ->
                    (wkns : SnocList Name) ->
                    List (RigCount, Term ((done ++ vars) ++ wkns))
mkConstantAppArgs lets fc [<] wkns = []
mkConstantAppArgs {done} {vars = xs :< x} lets fc (env :< b) wkns
    = let rec = mkConstantAppArgs {done} lets fc env (cons x wkns) in
          if lets || not (isLet b)
             then (multiplicity b,
                     Local fc (Just (isLet b)) (length wkns) (mkVar wkns)) ::
                       rewrite sym $ appendAssociative (done ++ xs) [<x] wkns in rec
             else rewrite sym $ appendAssociative (done ++ xs) [<x] wkns in rec

parameters {auto c : Ref Ctxt Defs} {auto u : Ref UST UState}

  addHoleName : FC -> Name -> Int -> Core ()
  addHoleName fc n i = update UST { holes $= insert i (fc, n),
                                    currentHoles $= insert i (fc, n) }

  -- Create a new metavariable with the given name and return type,
  -- and return a term which is the metavariable applied to the environment
  -- (and which has the given type)
  -- Flag whether to abstract over lets
  export
  newMetaLets : {vars : _} ->
                FC -> RigCount ->
                Env Term vars -> Name -> Term vars -> Def ->
                Bool ->
                Core (Int, Term vars)
  newMetaLets {vars} fc rig env n ty def lets
      = do let hty = if lets then abstractFullEnvType fc env ty
                             else abstractEnvType fc env ty
           let hole = newDef fc n rig hty Public def
           log "unify.meta" 5 $ "Adding new meta " ++ show (n, fc, rig)
           logTerm "unify.meta" 10 ("New meta type " ++ show n) hty
           idx <- addDef n hole
           addHoleName fc n idx
           pure (idx, Meta fc n idx envArgs)
    where
      envArgs : List (RigCount, Term vars)
      envArgs = let args = reverse (mkConstantAppArgs {done = [<]} lets fc env [<]) in
                    rewrite sym (appendLinLeftNeutral vars) in args

  export
  newMeta : {vars : _} ->
            FC -> RigCount ->
            Env Term vars -> Name -> Term vars -> Def ->
            Core (Int, Term vars)
  newMeta fc r env n ty def = newMetaLets fc r env n ty def False
