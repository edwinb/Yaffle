module Core.Transform

import Core.Context
import Core.Env
import Core.TT

import Libraries.Data.NameMap

import Data.Vect

%default total

unload : List (FC, RigCount, Term vars) -> Term vars -> Term vars
unload [] fn = fn
unload ((fc, c, arg) :: args) fn = unload args (App fc fn c arg)

-- List of matches on LHS
data MatchVars : SnocList Name -> SnocList Name -> Type where
     None : MatchVars lhsvars vs
     Match : (idx : Nat) -> (0 p : IsVar n idx lhsvars) -> Term vs ->
             MatchVars lhsvars vs -> MatchVars lhsvars vs

lookupMatch : (idx : Nat) -> (0 p : IsVar n idx lhsvars) -> MatchVars lhsvars vs ->
              Maybe (Term vs)
lookupMatch idx p None = Nothing
lookupMatch idx p (Match v _ val rest)
    = if idx == v
         then Just val
         else lookupMatch idx p rest

addMatch : (idx : Nat) -> (0 p : IsVar n idx lhsvars) -> Term vs ->
           MatchVars lhsvars vs -> Maybe (MatchVars lhsvars vs)
addMatch idx p val ms
    = case lookupMatch idx p ms of
           Nothing => Just (Match idx p val ms)
           Just val' => if eqTerm val val'
                           then Just ms
                           else Nothing

-- LHS of a rule must be a function application, so there's not much work
-- to do here!
match : MatchVars vars vs ->
        Term vars -> Term vs -> Maybe (MatchVars vars vs)
match ms (Local _ idx p) val
    = addMatch idx p val ms
match ms (App _ f _ a) (App _ f' _ a')
    = do ms' <- match ms f f'
         match ms' a a'
match ms x y
    = if eqTerm x y
         then Just ms
         else Nothing

covering
tryReplace : MatchVars vars vs -> Term vars -> Maybe (Term vs)
tryReplace ms (Local _ idx p) = lookupMatch idx p ms
tryReplace ms (Ref fc nt n) = pure (Ref fc nt n)
tryReplace ms (Meta fc n i as)
    = do as' <- traverse (\ (c, t) => Just (c, !(tryReplace ms t))) as
         pure (Meta fc n i as')
tryReplace ms (Bind fc x b sc)
    = Nothing -- TODO: can't do this yet... need to be able to weaken ms
              -- Rules are unlikely to have binders usually but we should
              -- still support it eventually
tryReplace ms (App fc f c a)
    = do f' <- tryReplace ms f
         a' <- tryReplace ms a
         pure (App fc f' c a')
tryReplace ms (As fc s a p)
    = Nothing -- No 'As' on RHS of a rule
tryReplace ms (Case{})
    = Nothing -- As for 'Bind', can't do this yet
tryReplace ms (TDelayed fc r tm)
    = do tm' <- tryReplace ms tm
         pure (TDelayed fc r tm')
tryReplace ms (TDelay fc r ty tm)
    = do ty' <- tryReplace ms ty
         tm' <- tryReplace ms tm
         pure (TDelay fc r ty' tm')
tryReplace ms (TForce fc r tm)
    = do tm' <- tryReplace ms tm
         pure (TForce fc r tm')
tryReplace ms (PrimVal fc c) = pure (PrimVal fc c)
tryReplace ms (PrimOp fc fn args)
    = do args' <- traverse (tryReplace ms) args
         pure (PrimOp fc fn args')
tryReplace ms (Erased fc Impossible) = pure (Erased fc Impossible)
tryReplace ms (Erased fc Placeholder) = pure (Erased fc Placeholder)
tryReplace ms (Erased fc (Dotted t)) = Erased fc . Dotted <$> tryReplace ms t
tryReplace ms (Unmatched fc s) = pure (Unmatched fc s)
tryReplace ms (TType fc u) = pure (TType fc u)

covering
tryApply : Transform -> Term vs -> Maybe (Term vs)
tryApply trans@(MkTransform {vars} n _ lhs rhs) tm
   = case match None lhs tm of
          Just ms => tryReplace ms rhs
          Nothing =>
            case tm of
                 App fc f c a =>
                     do f' <- tryApply trans f
                        Just (App fc f' c a)
                 _ => Nothing

apply : List Transform -> Term vars -> (Bool, Term vars)
apply [] tm = (False, tm)
apply (t :: ts) tm
    = case tryApply t tm of
           Nothing => apply ts tm
           Just res => (True, res)

data Upd : Type where

covering
trans : {auto c : Ref Ctxt Defs} ->
        {auto u : Ref Upd Bool} ->
        Env Term vars -> List (FC, RigCount, Term vars) -> Term vars ->
        Core (Term vars)
trans env stk (Ref fc Func fn)
    = do defs <- get Ctxt
         case lookup fn (transforms defs) of
              Nothing => pure (unload stk (Ref fc Func fn))
              Just ts => do let fullapp = unload stk (Ref fc Func fn)
                            let (u, tm') = apply ts fullapp
                            update Upd (|| u)
                            pure tm'
trans env stk (Meta fc n i args)
    = do args' <- traverse (\ (c, t) => pure (c, !(trans env [] t))) args
         pure $ unload stk (Meta fc n i args')
trans env stk (Bind fc x b sc)
    = do b' <- traverse (trans env []) b
         sc' <- trans (env :< b') [] sc
         pure $ unload stk (Bind fc x b' sc')
trans env stk (App fc fn c arg)
    = do arg' <- trans env [] arg
         trans env ((fc, c, arg') :: stk) fn
trans env stk (Case fc c sc scty alts)
    = do sc' <- trans env [] sc
         scty' <- trans env [] scty
         alts' <- traverse transAlt alts
         pure $ unload stk (Case fc c sc' scty' alts')
  where
    transScope : forall vars .
                 FC -> Env Term vars -> CaseScope vars -> Core (CaseScope vars)
    transScope fc env (RHS tm) = pure $ RHS !(trans env [] tm)
    transScope fc env (Arg c x sc)
        = let env' = env :< PVar fc c Explicit (Erased fc Placeholder) in
              pure $ Arg c x !(transScope fc env' sc)

    transAlt : CaseAlt vars -> Core (CaseAlt vars)
    transAlt (ConCase fc n t sc) = pure $ ConCase fc n t !(transScope fc env sc)
    transAlt (DelayCase fc t a sc)
        = let env' = env :<
                     PVar fc top Explicit (Erased fc Placeholder) :<
                     PVar fc erased Implicit (Erased fc Placeholder) in
              pure $ DelayCase fc t a !(trans env' [] sc)
    transAlt (ConstCase fc c tm) = pure $ ConstCase fc c !(trans env [] tm)
    transAlt (DefaultCase fc tm) = pure $ DefaultCase fc !(trans env [] tm)

trans env stk (TDelayed fc r tm)
    = do tm' <- trans env [] tm
         pure $ unload stk (TDelayed fc r tm')
trans env stk (TDelay fc r ty tm)
    = do ty' <- trans env [] ty
         tm' <- trans env [] tm
         pure $ unload stk (TDelay fc r ty' tm')
trans env stk (TForce fc r tm)
    = do tm' <- trans env [] tm
         pure $ unload stk (TForce fc r tm')
trans env stk (PrimOp fc fn args)
    = do args' <- traverseVect (trans env []) args
         pure $ unload stk (PrimOp fc fn args')
trans env stk tm = pure $ unload stk tm

covering
transLoop : {auto c : Ref Ctxt Defs} ->
            Nat -> Env Term vars -> Term vars -> Core (Term vars)
transLoop Z env tm = pure tm
transLoop (S k) env tm
    = do u <- newRef Upd False
         tm' <- trans env [] tm
         upd <- get Upd
         if upd -- If there was a transform applied, go around again until
                -- we hit the threshold
            then transLoop k env tm'
            else pure tm'

export
covering
applyTransforms : {auto c : Ref Ctxt Defs} ->
                  Env Term vars -> Term vars -> Core (Term vars)
applyTransforms env tm = transLoop 5 env tm
