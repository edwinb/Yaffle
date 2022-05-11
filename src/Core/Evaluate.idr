module Core.Evaluate

import Core.Context
import Core.Env
import Core.Error
import public Core.Evaluate.Convert
import public Core.Evaluate.Normalise
import public Core.Evaluate.Quote
import public Core.Evaluate.Value
import Core.TT

import Data.SnocList

parameters {auto c : Ref Ctxt Defs}
  export
  normalise
      : {vars : _} ->
        Env Term vars -> Term vars -> Core (Term vars)
  normalise env tm
      = do val <- nf env tm
           quoteNF env val

  export
  getArityVal : Value vars -> Core Nat
  getArityVal (VBind fc _ (Pi _ _ _ _) sc)
      = pure $ 1 + !(getArityVal !(sc (VErased fc False)))
  getArityVal _ = pure 0

  export
  getArity : {vars : _} -> Env Term vars -> Term vars -> Core Nat
  getArity env tm = getArityVal !(nf env tm)

  replace'
      : {vars : _} ->
        Int -> Env Term vars ->
        (orig : Value vars) -> (parg : Term vars) -> (tm : Value vars) ->
        Core (Term vars)
  replace' {vars} tmpi env orig parg tm
      = if !(convert env orig tm)
           then pure parg
           else repSub tm
    where
      repArg : Value vars -> Core (Term vars)
      repArg = replace' tmpi env orig parg

      repScope : FC -> Int -> (args : List Name) ->
                 VCaseScope args vars -> Core (CaseScope vars)
      repScope fc tmpi [] rhs
          = do rhs' <- replace' tmpi env orig parg !rhs
               pure (RHS rhs')
      repScope fc tmpi (x :: xs) scope
          = do let xn = MN "tmp" tmpi
               let xv = VApp fc Bound xn [<] (pure Nothing)
               scope' <- repScope fc (tmpi + 1) xs (scope xv)
               pure (Arg x (refsToLocalsCaseScope (Add x xn None) scope'))

      repAlt : FC -> VCaseAlt vars -> Core (CaseAlt vars)
      repAlt fc (VConCase n t args scope)
          = do scope' <- repScope fc tmpi args scope
               pure (ConCase n t scope')
      repAlt fc (VDelayCase ty arg scope)
          = do let tyn = MN "tmp" tmpi
               let argn = MN "tmp" (tmpi + 1)
               let tyv = VApp fc Bound tyn [<] (pure Nothing)
               let argv = VApp fc Bound argn [<] (pure Nothing)
               scope' <- replace' (tmpi + 2) env orig parg !(scope tyv argv)
               let rhs = refsToLocals (Add ty tyn (Add arg argn None)) scope'
               pure (DelayCase ty arg rhs)
      repAlt fc (VConstCase c rhs)
          = do rhs' <- repArg rhs
               pure (ConstCase c rhs')
      repAlt fc (VDefaultCase rhs)
          = do rhs' <- repArg rhs
               pure (DefaultCase rhs')

      repSub : Value vars -> Core (Term vars)
      repSub (VLam fc x c p ty scfn)
          = do b' <- traverse repSub (Lam fc c p ty)
               let x' = MN "tmp" tmpi
               let var = VApp fc Bound x' [<] (pure Nothing)
               sc' <- replace' (tmpi + 1) env orig parg !(scfn var)
               pure (Bind fc x b' (refsToLocals (Add x x' None) sc'))
      repSub (VBind fc x b scfn)
          = do b' <- traverse repSub b
               let x' = MN "tmp" tmpi
               let var = VApp fc Bound x' [<] (pure Nothing)
               sc' <- replace' (tmpi + 1) env orig parg !(scfn var)
               pure (Bind fc x b' (refsToLocals (Add x x' None) sc'))
      -- Perhaps we should have two variants here: one which just looks
      -- at the application (which is what we currently do) and one which
      -- evaluates further.
      repSub (VApp fc nt fn args val')
          = do args' <- traverseSnocList (traversePair repArg) args
               pure $ applyWithFC (Ref fc nt fn) (toList args')
      repSub (VLocal fc m idx p args)
          = do args' <- traverseSnocList (traversePair repArg) args
               pure $ applyWithFC (Local fc m idx p) (toList args')
      -- Look in value of the metavar if it's solved, otherwise leave it
      repSub (VMeta fc n i scope args val)
          = do Nothing <- val
                   | Just val' => repSub val'
               sc' <- traverse repArg scope
               args' <- traverseSnocList (traversePair repArg) args
               pure $ applyWithFC (Meta fc n i sc') (toList args')
      repSub (VDCon fc n t a args)
        = do args' <- traverseSnocList (traversePair repArg) args
             pure $ applyWithFC (Ref fc (DataCon t a) n) (toList args')
      repSub (VTCon fc n a args)
        = do args' <- traverseSnocList (traversePair repArg) args
             pure $ applyWithFC (Ref fc (TyCon a) n) (toList args')
      repSub (VAs fc s a pat)
          = do Local lfc _ i prf <- repSub a
                   | _ => repSub pat
               pat' <- repSub pat
               pure (As fc s (AsLoc lfc i prf) pat')
      repSub (VCase fc sc scty alts)
          = do sc' <- repArg sc
               scty' <- repArg scty
               alts' <- traverse (repAlt fc) alts
               pure (Case fc sc' scty' alts')
      repSub (VDelayed fc r tm)
          = do tm' <- repSub tm
               pure (TDelayed fc r tm')
      repSub (VDelay fc r ty tm)
          = do ty' <- repArg ty
               tm' <- repArg tm
               pure (TDelay fc r ty' tm')
      repSub (VForce fc r tm args)
          = do args' <- traverseSnocList (traversePair repArg) args
               tm' <- repSub tm
               pure $ applyWithFC (TForce fc r tm') (toList args')
      repSub tm = quote env tm

  export
  replace
      : {vars : _} ->
        Env Term vars ->
        (orig : Value vars) -> (new : Term vars) -> (tm : Value vars) ->
        Core (Term vars)
  replace = replace' 0
