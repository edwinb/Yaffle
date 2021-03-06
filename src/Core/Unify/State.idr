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

-- Unification mode and results
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

export
lower : UnifyInfo -> UnifyInfo
lower = { atTop := False }

export
Eq UnifyMode where
   InLHS == InLHS = True
   InTerm == InTerm = True
   InMatch == InMatch = True
   InSearch == InSearch = True
   _ == _ = False

export
Eq UnifyInfo where
  x == y = atTop x == atTop y && umode x == umode y

export
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

export
union : UnifyResult -> UnifyResult -> UnifyResult
union u1 u2 = MkUnifyResult (union (constraints u1) (constraints u2))
                            (holesSolved u1 || holesSolved u2)
                            (namesSolved u1 ++ namesSolved u2)
                            NoLazy -- only top level, so assume no annotation

export
unionAll : List UnifyResult -> UnifyResult
unionAll [] = MkUnifyResult [] False [] NoLazy
unionAll [c] = c
unionAll (c :: cs) = union c (unionAll cs)

export
constrain : Int -> UnifyResult
constrain c = MkUnifyResult [c] False [] NoLazy

export
success : UnifyResult
success = MkUnifyResult [] False [] NoLazy

export
solvedHole : Int -> UnifyResult
solvedHole n = MkUnifyResult [] True [n] NoLazy

export
ufail : FC -> String -> Core a
ufail loc msg = throw (GenericMsg loc msg)

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
  export
  resetNextVar : Core ()
  resetNextVar = update UST { nextName := 0 }

  -- Generate a global name based on the given root, in the current namespace
  export
  genName : String -> Core Name
  genName str
      = do ust <- get UST
           put UST ({ nextName $= (+1) } ust)
           n <- inCurrentNS (MN str (nextName ust))
           pure n

  -- Generate a global name based on the given name, in the current namespace
  export
  genMVName : Name -> Core Name
  genMVName (UN str) = genName (displayUserName str)
  genMVName (MN str _) = genName str
  genMVName n
      = do ust <- get UST
           put UST ({ nextName $= (+1) } ust)
           mn <- inCurrentNS (MN (show n) (nextName ust))
           pure mn

  -- Generate a unique variable name based on the given root
  export
  genVarName : String -> Core Name
  genVarName str
      = do ust <- get UST
           put UST ({ nextName $= (+1) } ust)
           pure (MN str (nextName ust))

  export
  genWithName : String -> Core Name
  genWithName root
      = do ust <- get UST
           put UST ({ nextName $= (+1) } ust)
           inCurrentNS (WithBlock root (nextName ust))

  addHoleName : FC -> Name -> Int -> Core ()
  addHoleName fc n i = update UST { holes $= insert i (fc, n),
                                    currentHoles $= insert i (fc, n) }

  addGuessName : FC -> Name -> Int -> Core ()
  addGuessName fc n i = update UST { guesses $= insert i (fc, n) }

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

  mkConstant : {vars : _} ->
               FC -> Env Term vars -> Term vars -> Term [<]
  mkConstant fc [<] tm = tm
  mkConstant {vars = _ :< x} fc (env :< b) tm
      = let ty = binderType b in
            mkConstant fc env (Bind fc x (Lam fc (multiplicity b) Explicit ty) tm)

  -- Given a term and a type, add a new guarded constant to the global context
  -- by applying the term to the current environment
  -- Return the replacement term (the name applied to the environment)
  export
  newConstant : {vars : _} ->
                FC -> RigCount -> Env Term vars ->
                (tm : Term vars) -> (ty : Term vars) ->
                (constrs : List Int) ->
                Core (Term vars)
  newConstant {vars} fc rig env tm ty constrs
      = do let def = mkConstant fc env tm
           let defty = abstractFullEnvType fc env ty
           cn <- genName "postpone"
           let guess = newDef fc cn rig defty Public
                              (Guess def (length env) constrs)
           log "unify.constant" 5 $ "Adding new constant " ++ show (cn, fc, rig)
           logTerm "unify.constant" 10 ("New constant type " ++ show cn) defty
           idx <- addDef cn guess
           addGuessName fc cn idx
           pure (Meta fc cn idx envArgs)
    where
      envArgs : List (RigCount, Term vars)
      envArgs = let args = reverse (mkConstantAppArgs {done = [<]} True fc env [<]) in
                    rewrite sym (appendLinLeftNeutral vars) in args

  export
  addConstraint : Constraint -> Core Int
  addConstraint constr
      = do ust <- get UST
           let cid = nextConstraint ust
           put UST ({ constraints $= insert cid constr,
                      nextConstraint := cid+1 } ust)
           pure cid

  export
  removeHole : Int -> Core ()
  removeHole n = update UST { holes $= delete n,
                              currentHoles $= delete n,
                              delayedHoles $= delete n }

  export
  removeHoleName : Name -> Core ()
  removeHoleName n
      = do defs <- get Ctxt
           whenJust (getNameID n defs.gamma) removeHole

  export
  tryErrorUnify : Core a -> Core (Either Error a)
  tryErrorUnify elab
      = do ust <- get UST
           defs <- branch
           catch (do res <- elab
                     commit
                     pure (Right res))
                 (\err => do put UST ust
                             defs' <- get Ctxt
                             put Ctxt defs
                             pure (Left err))

  export
  tryUnify : Core a -> Core a -> Core a
  tryUnify elab1 elab2
      = do Right ok <- tryErrorUnify elab1
                 | Left err => elab2
           pure ok

  export
  handleUnify : Core a -> (Error -> Core a) -> Core a
  handleUnify elab1 elab2
      = do Right ok <- tryErrorUnify elab1
                 | Left err => elab2 err
           pure ok
