module Core.Evaluate.Quote

-- Quoting evaluated values back to Terms

import Core.Context
import Core.Env
import Core.Error
import Core.TT
import Core.Evaluate.Value

import Data.Vect

data QVar : Type where

genName : Ref QVar Int => String -> Core Name
genName n
    = do i <- get QVar
         put QVar (i + 1)
         pure (MN n i)

data Strategy
  = NF -- full normal form
  | BlockApp -- block all applications

{-
On Strategy: when quoting to full NF, we still want to block the body of an
application if it turns out to be a case expression or primitive. This is
primarily for readability of the result because we want to see the function
that was blocked, not its complete definition.
-}

applySpine : Term vars -> SnocList (FC, Term vars) -> Term vars
applySpine tm [<] = tm
applySpine tm (args :< (fc, arg)) = App fc (applySpine tm args) arg

parameters {auto c : Ref Ctxt Defs} {auto q : Ref QVar Int}

  quoteGen : {bound, vars : _} ->
             Strategy -> Bounds bound -> Env Term vars ->
             Value vars -> Core (Term (bound ++ vars))

  -- probably ought to make traverse work on SnocList/Vect too
  quoteSpine : {bound, vars : _} ->
               Strategy -> Bounds bound -> Env Term vars ->
               Spine vars -> Core (SnocList (FC, Term (bound ++ vars)))
  quoteSpine s bounds env [<] = pure [<]
  quoteSpine s bounds env (args :< (fc, arg))
      = pure $ !(quoteSpine s bounds env args) :<
               (fc, !(quoteGen s bounds env arg))

  mkTmpVar : FC -> Name -> Value vars
  mkTmpVar fc n = VApp fc Bound n [<] (pure Nothing)

  quoteAlt : {bound, vars : _} ->
             FC -> Strategy -> Bounds bound -> Env Term vars ->
             VCaseAlt vars -> Core (CaseAlt (bound ++ vars))
  quoteAlt {vars} fc s bounds env (VConCase n t a sc)
      = do sc' <- quoteScope a bounds sc
           pure $ ConCase n t sc'
    where
      quoteScope : {bound : _} ->
                   (args : List Name) ->
                   Bounds bound ->
                   VCaseScope args vars ->
                   Core (CaseScope (bound ++ vars))
      quoteScope [] bounds rhs
          = do rhs' <- quoteGen s bounds env !rhs
               pure (RHS rhs')
      quoteScope (a :: as) bounds sc
          = do an <- genName "c"
               let sc' = sc (mkTmpVar fc an)
               rhs' <- quoteScope as (Add a an bounds) sc'
               pure (Arg a rhs')

  quoteAlt fc s bounds env (VDelayCase ty arg sc)
      = do tyn <- genName "ty"
           argn <- genName "arg"
           sc' <- quoteGen s (Add ty tyn (Add arg argn bounds)) env
                           !(sc (mkTmpVar fc tyn) (mkTmpVar fc argn))
           pure (DelayCase ty arg sc')
  quoteAlt fc s bounds env (VConstCase c sc)
      = do sc' <- quoteGen s bounds env sc
           pure (ConstCase c sc')
  quoteAlt fc s bounds env (VDefaultCase sc)
      = do sc' <- quoteGen s bounds env sc
           pure (DefaultCase sc')

  quotePi : {bound, vars : _} ->
            Strategy -> Bounds bound -> Env Term vars ->
            PiInfo (Value vars) -> Core (PiInfo (Term (bound ++ vars)))
  quotePi s bounds env Explicit = pure Explicit
  quotePi s bounds env Implicit = pure Implicit
  quotePi s bounds env AutoImplicit = pure AutoImplicit
  quotePi s bounds env (DefImplicit t)
      = do t' <- quoteGen s bounds env t
           pure (DefImplicit t')

  quoteBinder : {bound, vars : _} ->
                Strategy -> Bounds bound -> Env Term vars ->
                Binder (Value vars) -> Core (Binder (Term (bound ++ vars)))
  quoteBinder s bounds env (Lam fc r p ty)
      = do ty' <- quoteGen s bounds env ty
           p' <- quotePi s bounds env p
           pure (Lam fc r p' ty')
  quoteBinder s bounds env (Let fc r val ty)
      = do ty' <- quoteGen s bounds env ty
           val' <- quoteGen s bounds env val
           pure (Let fc r val' ty')
  quoteBinder s bounds env (Pi fc r p ty)
      = do ty' <- quoteGen s bounds env ty
           p' <- quotePi s bounds env p
           pure (Pi fc r p' ty')
  quoteBinder s bounds env (PVar fc r p ty)
      = do ty' <- quoteGen s bounds env ty
           p' <- quotePi s bounds env p
           pure (PVar fc r p' ty')
  quoteBinder s bounds env (PLet fc r val ty)
      = do ty' <- quoteGen s bounds env ty
           val' <- quoteGen s bounds env val
           pure (PLet fc r val' ty')
  quoteBinder s bounds env (PVTy fc r ty)
      = do ty' <- quoteGen s bounds env ty
           pure (PVTy fc r ty')

--   Declared above as:
--   quoteGen : {bound, vars : _} ->
--              Strategy -> Bounds bound -> Env Term vars ->
--              Value vars -> Core (Term (bound ++ vars))
  quoteGen s bounds env (VLam fc x c p ty sc)
      = do var <- genName "qv"
           p' <- quotePi s bounds env p
           ty' <- quoteGen s bounds env ty
           sc' <- quoteGen s (Add x var bounds) env
                             !(sc (mkTmpVar fc var))
           pure (Bind fc x (Lam fc c p' ty') sc')
  quoteGen s bounds env (VBind fc x b sc)
      = do var <- genName "qv"
           b' <- quoteBinder s bounds env b
           sc' <- quoteGen s (Add x var bounds) env
                             !(sc (mkTmpVar fc var))
           pure (Bind fc x b' sc')
  -- These are the names we invented when quoting the scope of a binder
  quoteGen s bounds env (VApp fc Bound (MN n i) sp val)
      = do sp' <- quoteSpine BlockApp bounds env sp
           case findName bounds of
                Just (MkVar p) =>
                    pure $ applySpine (Local fc Nothing _ (varExtend p)) sp'
                Nothing =>
                    pure $ applySpine (Ref fc Bound (MN n i)) sp'
    where
      findName : Bounds bound' -> Maybe (Var bound')
      findName None = Nothing
      findName (Add x (MN n' i') ns)
          = if i == i' -- this uniquely identifies it, given how we
                       -- generated the names, and is a faster test!
               then Just (MkVar First)
               else do MkVar p <-findName ns
                       Just (MkVar (Later p))
      findName (Add x _ ns)
          = do MkVar p <-findName ns
               Just (MkVar (Later p))
  quoteGen BlockApp bounds env (VApp fc nt n sp val)
      = do sp' <- quoteSpine BlockApp bounds env sp
           pure $ applySpine (Ref fc nt n) sp'
  quoteGen NF bounds env (VApp fc nt n sp val)
      = do Just v <- val
              | Nothing =>
                  do sp' <- quoteSpine NF bounds env sp
                     pure $ applySpine (Ref fc nt n) sp'
           quoteGen NF bounds env v
  quoteGen {bound} s bounds env (VLocal fc mlet idx p sp)
      = do sp' <- quoteSpine s bounds env sp
           let MkVar p' = addLater bound p
           pure $ applySpine (Local fc mlet _ p') sp'
    where
      addLater : {idx : _} ->
                 (ys : List Name) -> (0 p : IsVar n idx xs) ->
                 Var (ys ++ xs)
      addLater [] isv = MkVar isv
      addLater (x :: xs) isv
          = let MkVar isv' = addLater xs isv in
                MkVar (Later isv')
  quoteGen BlockApp bounds env (VMeta fc n i args sp val)
      = do sp' <- quoteSpine BlockApp bounds env sp
           args' <- traverse (quoteGen BlockApp bounds env) args
           pure $ applySpine (Meta fc n i args') sp'
  quoteGen s bounds env (VMeta fc n i args sp val)
      = do Just v <- val
              | Nothing =>
                  do sp' <- quoteSpine BlockApp bounds env sp
                     args' <- traverse (quoteGen BlockApp bounds env) args
                     pure $ applySpine (Meta fc n i args') sp'
           quoteGen s bounds env v
  quoteGen s bounds env (VDCon fc n t a sp)
      = do sp' <- quoteSpine s bounds env sp
           pure $ applySpine (Ref fc (DataCon t a) n) sp'
  quoteGen s bounds env (VTCon fc n a sp)
      = do sp' <- quoteSpine s bounds env sp
           pure $ applySpine (Ref fc (TyCon a) n) sp'
  quoteGen s bounds env (VAs fc use as pat) = ?quoteAs
  quoteGen s bounds env (VCase fc sc scTy alts)
      = do sc' <- quoteGen s bounds env sc
           scTy' <- quoteGen s bounds env scTy
           alts' <- traverse (quoteAlt fc s bounds env) alts
           pure $ Case fc sc' scTy' alts'
  quoteGen s bounds env (VDelayed fc r ty) = ?quoteDelayed
  quoteGen s bounds env (VDelay fc r ty arg) = ?quoteDelay
  quoteGen s bounds env (VForce fc r val sp) = ?quoteForce
  quoteGen s bounds env (VPrimVal fc c) = pure $ PrimVal fc c
  quoteGen {vars} {bound} s bounds env (VPrimOp fc fn args)
      = do args' <- quoteArgs args
           pure $ PrimOp fc fn args'
    where
      -- No traverse for Vect in Core...
      quoteArgs : Vect n (Value vars) -> Core (Vect n (Term (bound ++ vars)))
      quoteArgs [] = pure []
      quoteArgs (a :: as)
          = pure $ !(quoteGen s bounds env a) :: !(quoteArgs as)
  quoteGen s bounds env (VErased fc i) = pure $ Erased fc i
  quoteGen s bounds env (VUnmatched fc str) = pure $ Unmatched fc str
  quoteGen s bounds env (VImpossible fc) = pure $ Impossible fc
  quoteGen s bounds env (VType fc n) = pure $ TType fc n

export
quoteNF : {vars : _} ->
          Ref Ctxt Defs =>
          Env Term vars -> Value vars -> Core (Term vars)
quoteNF env val
    = do q <- newRef QVar 0
         quoteGen NF None env val

export
quote : {vars : _} ->
        Ref Ctxt Defs =>
        Env Term vars -> Value vars -> Core (Term vars)
quote env val
    = do q <- newRef QVar 0
         quoteGen BlockApp None env val
