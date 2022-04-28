module Core.Evaluate.Convert

import Core.Context
import Core.Core
import Core.Env
import Core.Error
import Core.TT
import Core.TT.Universes

import Core.Evaluate.Normalise
import Core.Evaluate.Value

import Data.SnocList
import Data.Vect

data QVar : Type where

data Strategy
  = Reduce -- reduce applications
  | BlockApp -- block all applications. This is for when we've gone under a
             -- case so applications will be stuck

genName : Ref QVar Int => String -> Core Name
genName n
    = do i <- get QVar
         put QVar (i + 1)
         pure (MN n i)

genVar : Ref QVar Int => FC -> String -> Core (Value vars)
genVar fc n
    = do var <- genName n
         pure (VApp fc Bound var [<] (pure Nothing))

parameters {auto c : Ref Ctxt Defs}

  convGen : {vars : _} ->
            Ref QVar Int =>
            Strategy -> Env Term vars ->
            Value vars -> Value vars -> Core Bool

  convSpine : {vars : _} ->
              Ref QVar Int =>
              Strategy -> Env Term vars ->
              Spine vars -> Spine vars -> Core Bool
  convSpine s env [<] [<] = pure True
  convSpine s env (xs :< (_, x)) (ys :< (_, y))
      = do True <- convGen s env x y | False => pure False
           convSpine s env xs ys
  convSpine s env _ _ = pure False

  -- Declared above
  -- convGen : {vars : _} ->
  --           Ref QVar Int =>
  --           Strategy -> Env Term vars ->
  --           Value vars -> Value vars -> Core Bool
  convGen s env (VLam fc x r p ty sc) (VLam fc' x' r' p' ty' sc')
      = do True <- convGen s env ty ty' | False => pure False
           var <- genVar fc "conv"
           convGen s env !(sc var) !(sc' var)
  convGen {vars} s env tmx@(VLam fc x r p ty sc) tmy
      = do let etay = VLam fc x r p ty (apply fc tmy)
           convGen s env tmx etay
  convGen {vars} s env tmx tmy@(VLam fc x r p ty sc)
      = do let etax = VLam fc x r p ty (apply fc tmy)
           convGen s env etax tmy
  convGen {vars} s env (VBind fc x b sc) (VBind fc' x' b' sc')
      = do True <- convBinders b b' | False => pure False
           var <- genVar fc "conv"
           convGen s env !(sc var) !(sc' var)
    where
      convBinders : Binder (Value vars) -> Binder (Value vars) -> Core Bool
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
      = do if n == n'
              then convSpine BlockApp env args args'
              else pure False
  convGen Reduce env x@(VApp _ _ _ _ val) y@(VApp _ _ _ _ val')
      = do -- Check without reducing first since it might save a lot of work
           -- on success
           False <- convGen BlockApp env x y | True => pure True
           Just x <- val  | Nothing => pure False
           Just y <- val' | Nothing => pure False
           convGen Reduce env x y
  convGen s env (VLocal _ _ i _ sp) (VLocal _ _ i' _ sp')
      = if i == i'
           then convSpine s env sp sp'
           else pure False
  convGen {vars} BlockApp env (VMeta fc n i sc args _) (VMeta _ n' i' sc' args' _)
      = do True <- convScope sc sc' | False => pure False
           convSpine BlockApp env args args'
    where
      convScope : List (Value vars) -> List (Value vars) -> Core Bool
      convScope [] [] = pure True
      convScope (x :: xs) (y :: ys)
          = do True <- convGen BlockApp env x y | False => pure False
               convScope xs ys
      convScope _ _ = pure False
  convGen {vars} Reduce env x@(VMeta _ _ _ _ _ val) y@(VMeta _ _ _ _ _ val')
      = do -- Check without reducing first since it might save a lot of work
           -- on success
           False <- convGen BlockApp env x y | True => pure True
           Just x <- val  | Nothing => pure False
           Just y <- val' | Nothing => pure False
           convGen Reduce env x y
  convGen s env (VDCon _ n t a sp) (VDCon _ n' t' a' sp')
      = if t == t'
           then convSpine s env sp sp'
           else pure False
  convGen s env (VTCon _ n a sp) (VTCon _ n' a' sp')
      = if n == n'
           then convSpine s env sp sp'
           else pure False
  convGen s env (VAs _ _ _ x) (VAs _ _ _ y) = convGen s env x y
  convGen {vars} s env (VCase fc sc ty alts) (VCase _ sc' ty' alts')
      = do True <- convGen s env sc sc' | False => pure False
           True <- convGen s env ty ty' | False => pure False
           convAlts alts alts'
   where
     convScope : (args : List Name) ->
                 VCaseScope args vars ->
                 (args' : List Name) ->
                 VCaseScope args' vars ->
                 Core Bool
     convScope [] sc [] sc' = convGen s env !sc !sc'
     convScope (x :: xs) sc (y :: ys) sc'
         = do xn <- genVar fc "arg"
              convScope xs (sc xn) ys (sc' xn)
     convScope _ _ _ _ = pure False

     convAlt : VCaseAlt vars -> VCaseAlt vars -> Core Bool
     convAlt (VConCase n t args sc) (VConCase n' t' args' sc')
         = if t == t'
              then convScope args sc args' sc'
              else pure False
     convAlt (VDelayCase t a sc) (VDelayCase t' a' sc')
         = do tn <- genVar fc "t"
              an <- genVar fc "a"
              convGen s env !(sc tn an) !(sc' tn an)
     convAlt (VConstCase c x) (VConstCase c' y)
         = if c == c'
              then convGen s env x y
              else pure False
     convAlt (VDefaultCase x) (VDefaultCase y) = convGen s env x y
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
      convArgs : Vect n (Value vars) -> Vect m (Value vars) -> Core Bool
      convArgs [] [] = pure True
      convArgs (x :: xs) (y :: ys)
          = do True <- convGen s env x y
                    | False => pure False
               convArgs xs ys
      convArgs _ _ = pure False
  convGen s env (VErased _ _) _ = pure True
  convGen s env _ (VErased _ _) = pure True
  convGen s env (VImpossible _) (VImpossible _) = pure True
  convGen s env (VType fc n) (VType fc' n')
      = do addConstraint (ULE fc n n')
           pure True
  convGen s env _ _ = pure False

  namespace Value
    export
    convert : {vars : _} ->
              Env Term vars -> Value vars -> Value vars -> Core Bool
    convert env x y
        = do q <- newRef QVar 0
             convGen Reduce env x y

  namespace Term
    export
    convert : {vars : _} ->
              Env Term vars -> Term vars -> Term vars -> Core Bool
    convert env x y
        = do x' <- nf env x
             y' <- nf env y
             convert env x' y'
