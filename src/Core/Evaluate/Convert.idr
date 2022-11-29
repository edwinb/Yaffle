module Core.Evaluate.Convert

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.Error
import Core.Evaluate.Quote
import Core.TT
import Core.TT.Universes

import Core.Evaluate.Normalise
import Core.Evaluate.Value

import Data.SnocList
import Data.Vect

data QVar : Type where

data Strategy
  = Reduce (List Namespace) -- reduce applications, as long as we're
             -- in a namespace where the definition is visible
  | BlockApp -- block all applications. This is for when we've gone under a
             -- case so applications will be stuck

genName : Ref QVar Int => String -> Core Name
genName n
    = do i <- get QVar
         put QVar (i + 1)
         pure (MN n i)

genVar : Ref QVar Int => FC -> String -> Core (Value f vars)
genVar fc n
    = do var <- genName n
         pure (VApp fc Bound var [<] (pure Nothing))

parameters {auto c : Ref Ctxt Defs}

  convGen : {vars : _} ->
            Ref QVar Int =>
            Strategy -> Env Term vars ->
            Value f vars -> Value f' vars -> Core Bool

  convSpine : {vars : _} ->
              Ref QVar Int =>
              Strategy -> Env Term vars ->
              Spine vars -> Spine vars -> Core Bool
  convSpine s env [<] [<] = pure True
  convSpine s env (xs :< (_, _, x)) (ys :< (_, _, y))
      = do True <- convGen s env x y | False => pure False
           convSpine s env xs ys
  convSpine s env _ _ = pure False

  -- Declared above
  -- convGen : {vars : _} ->
  --           Ref QVar Int =>
  --           Strategy -> Env Term vars ->
  --           Value vars -> Value f vars -> Core Bool
  convGen s env (VLam fc x r p ty sc) (VLam fc' x' r' p' ty' sc')
      = do True <- convGen s env ty ty' | False => pure False
           var <- genVar fc "conv"
           convGen s env !(sc var) !(sc' var)
  convGen {vars} s env tmx@(VLam fc x r p ty sc) tmy
      = do let etay = VLam fc x r p ty (apply fc tmy r)
           convGen {f'=Normal} s env tmx etay
  convGen {vars} s env tmx tmy@(VLam fc x r p ty sc)
      = do let etax = VLam fc x r p ty (apply fc tmy r)
           convGen {f=Normal} s env etax tmy
  convGen {vars} s env (VBind fc x b sc) (VBind fc' x' b' sc')
      = do True <- convBinders b b' | False => pure False
           var <- genVar fc "conv"
           convGen s env !(sc var) !(sc' var)
    where
      convBinders : Binder (Value f vars) -> Binder (Value f' vars) -> Core Bool
      convBinders (Lam _ cx _ tx) (Lam _ cy _ ty)
          = if cx /= cy
               then pure False
               else convGen s env tx ty
      convBinders (Pi _ cx _ tx) (Pi _ cy _ ty)
          = if cx /= cy
               then pure False
               else convGen s env tx ty
      convBinders _ _ = pure False
  convGen BlockApp env (VApp _ nt n args _) (VApp _ nt' n' args' _)
      = if n == n'
           then convSpine BlockApp env args args'
           else pure False
  convGen (Reduce ns) env x@(VApp fc _ n args val) y@(VApp fc' _ n' args' val')
      = do -- Check without reducing first since it might save a lot of work
           -- on success
           False <- convGen BlockApp env x y | True => pure True
           Just x' <- tryReduce fc n val  | Nothing => pure False
           Just y' <- tryReduce fc' n' val' | Nothing => pure False
           convGen (Reduce ns) env x' y'
    where
      -- Try reducing the application, but only if the name is one that's
      -- reducible in any of the given namespaces
      tryReduce : FC -> Name -> Core (Maybe (Glued vars)) ->
                  Core (Maybe (Glued vars))
      tryReduce fc n val
          = do v <- getVisibility fc n
               if reducibleInAny ns n v
                  then val
                  else pure Nothing
  -- If one is an App and the other isn't, try to reduce the App first
  convGen s env (VApp _ _ _ _ val) y
      = do Just x <- val | Nothing => pure False
           convGen s env x y
  convGen s env x (VApp _ _ _ _ val)
      = do Just y <- val | Nothing => pure False
           convGen s env x y
  convGen s env (VLocal _ i _ sp) (VLocal _ i' _ sp')
      = if i == i'
           then convSpine s env sp sp'
           else pure False
  convGen {vars} s env x@(VMeta _ _ i sc args val) y@(VMeta _ _ i' sc' args' val')
      = do Just x <- val  | Nothing => convMeta
           Just y <- val' | Nothing => convMeta
           convGen s env x y
    where
      convScope : List (RigCount, Glued vars) ->
                  List (RigCount, Glued vars) -> Core Bool
      convScope [] [] = pure True
      convScope ((_, x) :: xs) ((_, y) :: ys)
          = do True <- convGen s env x y | False => pure False
               convScope xs ys
      convScope _ _ = pure False

      convMeta : Core Bool
      convMeta
          = if i == i'
               then do True <- convScope sc sc' | False => pure False
                       convSpine s env args args'
               else pure False
  -- If one is a Metavar and the other isn't, try to reduce the Metavar first
  convGen s env (VMeta _ _ _ _ _ val) y
      = do Just x <- val | Nothing => pure False
           convGen s env x y
  convGen s env x (VMeta _ _ _ _ _ val)
      = do Just y <- val | Nothing => pure False
           convGen s env x y
  convGen s env (VDCon _ n t a sp) (VDCon _ n' t' a' sp')
      = if t == t'
           then convSpine s env sp sp'
           else pure False
  convGen s env (VTCon _ n a sp) (VTCon _ n' a' sp')
      = if n == n'
           then convSpine s env sp sp'
           else pure False
  convGen s env (VAs _ _ _ x) (VAs _ _ _ y) = convGen s env x y
  convGen {vars} s env (VCase fc r sc ty alts) (VCase _ r' sc' ty' alts')
      = do True <- convGen s env sc sc' | False => pure False
           True <- convGen s env ty ty' | False => pure False
           convAlts alts alts'
   where
     convScope : (args : SnocList (RigCount, Name)) ->
                 VCaseScope args vars ->
                 (args' : SnocList (RigCount, Name)) ->
                 VCaseScope args' vars ->
                 Core Bool
     convScope [<] sc [<] sc' = convGen BlockApp env !sc !sc'
     convScope (xs :< x) sc (ys :< y) sc'
         = do xn <- genVar fc "arg"
              convScope xs (sc xn) ys (sc' xn)
     convScope _ _ _ _ = pure False

     convAlt : VCaseAlt vars -> VCaseAlt vars -> Core Bool
     convAlt (VConCase _ n t args sc) (VConCase _ n' t' args' sc')
         = if t == t'
              then convScope args sc args' sc'
              else pure False
     convAlt (VDelayCase _ t a sc) (VDelayCase _ t' a' sc')
         = do tn <- genVar fc "t"
              an <- genVar fc "a"
              convGen BlockApp env !(sc tn an) !(sc' tn an)
     convAlt (VConstCase _ c x) (VConstCase _ c' y)
         = if c == c'
              then convGen BlockApp env x y
              else pure False
     convAlt (VDefaultCase _ x) (VDefaultCase _ y) = convGen BlockApp env x y
     convAlt _ _ = pure False

     convAlts : List (VCaseAlt vars) -> List (VCaseAlt vars) -> Core Bool
     convAlts [] [] = pure True
     convAlts (x :: xs) (y :: ys)
         = do True <- convAlt x y | False => pure False
              convAlts xs ys
     convAlts _ _ = pure False
  convGen s env (VDelayed _ r x) (VDelayed _ r' y)
      = if compatible r r'
           then convGen s env x y
           else pure False
  convGen s env (VDelay _ r _ x) (VDelay _ r' _ y)
      = if compatible r r'
           then convGen s env x y
           else pure False
  convGen s env (VForce _ r x spx) (VForce _ r' y spy)
      = if compatible r r'
           then do True <- convGen s env x y
                       | False => pure False
                   convSpine s env spx spy
           else pure False

  convGen s env (VPrimVal _ c) (VPrimVal _ c') = pure $ c == c'
  convGen {vars} s env (VPrimOp _ fn args) (VPrimOp _ fn' args')
      = if sameFn fn fn'
           then convArgs args args'
           else pure False
    where
      convArgs : Vect n (Value f vars) -> Vect m (Value f' vars) -> Core Bool
      convArgs [] [] = pure True
      convArgs (x :: xs) (y :: ys)
          = do True <- convGen s env x y
                    | False => pure False
               convArgs xs ys
      convArgs _ _ = pure False
  convGen s env (VErased _ (Dotted t)) u = convGen s env t u
  convGen s env t (VErased _ (Dotted u)) = convGen s env t u
  convGen s env (VErased _ _) _ = pure True
  convGen s env _ (VErased _ _) = pure True
  convGen s env (VType fc n) (VType fc' n')
      = do addConstraint (ULE fc n fc' n')
           pure True
  convGen s env _ _ = pure False

  namespace Value
    export
    convert : {vars : _} ->
              Env Term vars -> Value f vars -> Value f' vars -> Core Bool
    convert env x y
        = do q <- newRef QVar 0
             defs <- get Ctxt
             convGen (Reduce (currentNS defs :: nestedNS defs)) env x y

    export
    chkConvert : {vars : _} ->
                 FC -> Env Term vars -> Value f vars -> Value f' vars -> Core ()
    chkConvert fc env x y
        = do True <- convert env x y
                 | False => throw (CantConvert fc !(get Ctxt) env
                                               !(quote env x)
                                               !(quote env y))
             pure ()

  namespace Term
    export
    convert : {vars : _} ->
              Env Term vars -> Term vars -> Term vars -> Core Bool
    convert env x y
        = do x' <- nf env x
             y' <- nf env y
             convert env x' y'

    export
    chkConvert : {vars : _} ->
                 FC -> Env Term vars -> Term vars -> Term vars -> Core ()
    chkConvert fc env x y
        = do True <- convert env x y
                 | False => throw (CantConvert fc !(get Ctxt) env x y)
             pure ()
