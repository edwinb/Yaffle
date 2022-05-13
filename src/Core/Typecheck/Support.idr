module Core.Typecheck.Support

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
    go acc (Local _ _ _ p) tm
        = (MkVar p, tm) :: acc
    go acc tmx tmy = []
