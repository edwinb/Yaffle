module Core.Typecheck.Support

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
              (Var (x :: vars), Term (x :: vars)) ->
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
    goBinder acc (Lam _ _ _ ty) (Lam _ _ _ ty') = go acc ty ty'
    goBinder acc (Let _ _ val ty) (Let _ _ val' ty')
        = go (go acc val val') ty ty'
    goBinder acc (Pi _ _ _ ty) (Pi _ _ _ ty') = go acc ty ty'
    -- We're not going to see this, but for completeness
    goBinder acc (PVar _ _ _ ty) (PVar _ _ _ ty') = go acc ty ty'
    goBinder acc (PLet _ _ val ty) (PLet _ _ val' ty')
        = go (go acc val val') ty ty'
    goBinder acc (PVTy _ _ ty) (PVTy _ _ ty') = go acc ty ty'
    goBinder acc _ _ = []

    go acc (Local _ _ _ p) tm
        = (MkVar p, tm) :: acc
    go acc (Bind _ x b sc) (Bind _ x' b' sc')
        = let sc' = renameTop _ sc'
              scMatch = mapMaybe dropVar (go [] sc sc') in
              goBinder (scMatch ++ acc) b b'
    go acc (App _ f a) (App _ f' a')
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
