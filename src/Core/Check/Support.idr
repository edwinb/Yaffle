module Core.Check.Support

import Core.Context
import Core.Evaluate
import Core.TT

-- Match the first term against the second, returning all the expressions
-- that the variables match against.
-- If there's no match, return an empty list.
-- (Used in type-checking simple case expressions)
export
matchVars : Term vars -> Term vars -> List (Var vars, Term vars)
matchVars = go []
  where
    -- If we find matches under binders, we're only interested in the
    -- variables in the top level term, so drop things that are in the inner
    -- scope
    dropVar : forall vars .
              (Var (vars :< x), Term (vars :< x)) ->
              Maybe (Var vars, Term vars)
    dropVar (v, tm)
        = do v' <- removeVar zero v
             tm' <- shrinkTerm tm (DropCons SubRefl)
             pure (v', tm')

    go : forall vars .
         List (Var vars, Term vars) -> Term vars -> Term vars ->
         List (Var vars, Term vars)

    goBinder : forall vars .
         List (Var vars, Term vars) -> Binder (Term vars) -> Binder (Term vars) ->
         List (Var vars, Term vars)
    goBinder acc (MkBinder _ _ (LamVal _) ty) (MkBinder _ _ (LamVal _) ty') = go acc ty ty'
    goBinder acc (MkBinder _ _ (LetVal val) ty) (MkBinder _ _ (LetVal val') ty')
        = go (go acc val val') ty ty'
    goBinder acc (MkBinder _ _ (BPiVal _) ty) (MkBinder _ _ (BPiVal _) ty') = go acc ty ty'
    -- We're not going to see this, but for completeness
    goBinder acc (MkBinder _ _ (PVarVal _) ty) (MkBinder _ _ (PVarVal _) ty') = go acc ty ty'
    goBinder acc (MkBinder _ _ (PLetVal val) ty) (MkBinder _ _ (PLetVal val') ty')
        = go (go acc val val') ty ty'
    goBinder acc (MkBinder _ _ PVTyVal ty) (MkBinder _ _ PVTyVal ty') = go acc ty ty'
    goBinder acc _ _ = []

    go acc (Local _ _ _ p) tm
        = (MkVar p, tm) :: acc
    go acc (Bind _ x b sc) (Bind _ x' b' sc')
        = let sc' = renameTop _ sc'
              scMatch = mapMaybe dropVar (go [] sc sc') in
              goBinder (scMatch ++ acc) b b'
    go acc (App _ f _ a) (App _ f' _ a')
        = go (go acc f f') a a'
    -- TODO: This is enough to get us going, but better do the other cases ASAP!
    -- While we won't use the Raw typechecker in actual elaboration, it will
    -- still be useful for debugging/rechecking so this needs to be complete.
    go acc tmx tmy = []

export
replaceMatches : Ref Ctxt Defs =>
                 {vars : _} ->
                 FC -> Env Term vars -> List (Var vars, Term vars) ->
                 Term vars -> Core (Term vars)
replaceMatches fc env [] tm = pure tm
replaceMatches fc env ((MkVar p, orig) :: ms) tm
    = do tm' <- replaceMatches fc env ms tm
         replace env !(nf env orig) (Local fc Nothing _ p) !(nf env tm')
