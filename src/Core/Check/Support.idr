module Core.Check.Support

import Core.Context
import Core.Evaluate
import Core.TT

import Data.SnocList
import Data.Vect

import Libraries.Data.LengthMatch

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

    renameNTopScope : forall vars .
                      (ms : SnocList Name) ->
                      LengthMatch ns ms ->
                      CaseScope (vars ++ ns) -> CaseScope (vars ++ ms)
    renameNTopScope ms ok (RHS tm) = RHS (renameNTop ms ok tm)
    renameNTopScope ms ok (Arg r x sc)
        = Arg r x (renameNTopScope {ns = ns :< x} (ms :< x) (SnocMatch ok) sc)

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

    goPrimOp : forall vars .
               List (Var vars, Term vars) -> Vect ar (Term vars) -> Vect ar' (Term vars) ->
               List (Var vars, Term vars)
    goPrimOp acc (tm :: tms) (tm' :: tms') = goPrimOp (go acc tm tm') tms tms'
    goPrimOp acc _ _ = []

    goCaseScope : forall vars .
                  List (Var vars, Term vars) -> CaseScope vars -> CaseScope vars ->
                  List (Var vars, Term vars)
    goCaseScope acc (RHS tm) (RHS tm') = go acc tm tm'
    goCaseScope acc (Arg _ n sc) (Arg _ n' sc')
        = let sc' = renameNTopScope {ns = [<n']} [<n] (SnocMatch LinMatch) sc'
              scMatch = mapMaybe dropVar (goCaseScope [] sc sc') in
              scMatch ++ acc
    goCaseScope acc _ _ = []

    goCaseAlt : forall vars .
                List (Var vars, Term vars) -> CaseAlt vars -> CaseAlt vars ->
                List (Var vars, Term vars)
    goCaseAlt acc (ConCase _ _ _ sc) (ConCase _ _ _ sc')
        = goCaseScope acc sc sc'
    goCaseAlt acc (DelayCase _ n a tm) (DelayCase _ n' a' tm')
        = let tm' = renameNTop {ns = [<a', n']} [<a, n] (SnocMatch (SnocMatch LinMatch)) tm'
              scMatch = mapMaybe (dropVar <=< dropVar) (go [] tm tm') in
              scMatch ++ acc
    goCaseAlt acc (ConstCase _ _ tm) (ConstCase _ _ tm') = go acc tm tm'
    goCaseAlt acc (DefaultCase _ tm) (DefaultCase _ tm') = go acc tm tm'
    goCaseAlt acc _ _ = []

    goCaseAlts : forall vars .
                 List (Var vars, Term vars) -> List (CaseAlt vars) -> List (CaseAlt vars) ->
                 List (Var vars, Term vars)
    goCaseAlts acc (ca :: cas) (ca' :: cas') = goCaseAlts (goCaseAlt acc ca ca') cas cas'
    goCaseAlts acc _ _ = []

    go acc (Local _ _ p) tm
        = (MkVar p, tm) :: acc
    go acc (Bind _ x b sc) (Bind _ x' b' sc')
        = let sc' = renameTop _ sc'
              scMatch = mapMaybe dropVar (go [] sc sc') in
              goBinder (scMatch ++ acc) b b'
    go acc (App _ f _ a) (App _ f' _ a')
        = go (go acc f f') a a'
    go acc (As _ _ _ pat) (As _ _ _ pat')
        = go acc pat pat'
    go acc (Case _ _ sc scTy cs) (Case _ _ sc' scTy' cs')
        = goCaseAlts (go (go acc sc sc') scTy scTy') cs cs'
    go acc (TDelayed _ _ tm) (TDelayed _ _ tm')
        = go acc tm tm'
    go acc (TDelay _ _ ty arg) (TDelay _ _ ty' arg')
        = go (go acc ty ty') arg arg'
    go acc (TForce _ _ tm) (TForce _ _ tm')
        = go acc tm tm'
    go acc (PrimOp _ _ args) (PrimOp _ _ args')
        = goPrimOp acc args args'
    go acc tmx tmy = []

export
replaceMatches : Ref Ctxt Defs =>
                 {vars : _} ->
                 FC -> Env Term vars -> List (Var vars, Term vars) ->
                 Term vars -> Core (Term vars)
replaceMatches fc env [] tm = pure tm
replaceMatches fc env ((MkVar p, orig) :: ms) tm
    = do tm' <- replaceMatches fc env ms tm
         replace env !(nf env orig) (Local fc _ p) !(nf env tm')
