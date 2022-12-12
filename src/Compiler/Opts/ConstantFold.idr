module Compiler.Opts.ConstantFold

import Compiler.CompileExpr
import Core.Context
import Core.Context.Log
import Core.Evaluate
import Core.Primitives
import Core.TT.Name
import Data.List
import Data.SnocList
import Data.Vect

findConstAlt : Constant -> List (CConstAlt vars) ->
               Maybe (CExp vars) -> Maybe (CExp vars)
findConstAlt c [] def = def
findConstAlt c (MkConstAlt c' exp :: alts) def = if c == c'
    then Just exp
    else findConstAlt c alts def

foldableOp : PrimFn ar -> Bool
foldableOp BelieveMe = False
foldableOp (Cast IntType _) = False
foldableOp (Cast _ IntType) = False
foldableOp (Cast from to)   = isJust (intKind from) && isJust (intKind to)
foldableOp _                = True

data Subst : SnocList Name -> SnocList Name -> Type where
  Lin  : Subst [<] vars
  (:<) : Subst ds vars -> CExp vars -> Subst (ds :< d) vars
  Wk   : Subst ds vars -> SizeOf ws -> Subst (ds ++ ws) (vars ++ ws)

initSubst : (vars : SnocList Name) -> Subst vars vars
initSubst vars
  = rewrite sym $ appendLinLeftNeutral vars in
    Wk [<] (mkSizeOf vars)

wk : Subst ds vars ->
     SizeOf out ->
     Subst (ds ++ out) (vars ++ out)
wk (Wk {ws, ds, vars} rho sws) sout
    = rewrite sym $ appendAssociative ds ws out in
      rewrite sym $ appendAssociative vars ws out in
      Wk rho (sout + sws)
wk rho ws = Wk rho ws

record WkCExp (vars : SnocList Name) where
  constructor MkWkCExp
  {0 outer, supp : SnocList Name}
  size : SizeOf outer
  0 prf : vars === supp ++ outer
  expr : CExp supp

Weaken WkCExp where
  weaken (MkWkCExp s Refl e) = MkWkCExp (suc s) Refl e

lookup : FC -> Var ds -> Subst ds vars -> CExp vars
lookup fc (MkVar p) rho = case go p rho of
    Left (MkVar p') => CLocal fc p'
    Right (MkWkCExp s Refl e) => weakenNs s e

  where

  go : {i : Nat} -> {0 ds, vars : _} -> (0 _ : IsVar n i ds) ->
       Subst ds vars -> Either (Var vars) (WkCExp vars)
  go First     (rho :< val) = Right (MkWkCExp zero Refl val)
  go (Later p) (rho :< val) = go p rho
  go p         (Wk rho ws) = case sizedView ws of
    Z => go p rho
    S ws' => case i of
      Z => Left (MkVar First)
      S i' => bimap later weaken (go (dropLater p) (Wk rho ws'))

-- constant folding of primitive functions
-- if a primitive function is applied to only constant
-- then replace with the result
-- if there's only 1 constant argument to a commutative function
-- move the constant to the right. This simplifies Compiler.Opts.Identity
constFold : {vars' : _} ->
            Subst vars vars' ->
            CExp vars -> CExp vars'
constFold rho (CLocal fc p) = lookup fc (MkVar p) rho
constFold rho e@(CRef fc x) = CRef fc x
constFold rho (CLam fc x y)
  = CLam fc x $ constFold (wk rho (mkSizeOf [<x])) y
constFold rho (CLet fc x inlineOK y z) =
    let val = constFold rho y
     in case val of
        CPrimVal _ _ => if inlineOK
            then constFold (rho :< val) z
            else CLet fc x inlineOK val (constFold (wk rho (mkSizeOf [<x])) z)
        _ => CLet fc x inlineOK val (constFold (wk rho (mkSizeOf [<x])) z)
constFold rho (CApp fc (CRef fc2 n) [x]) =
  if n == NS typesNS (UN $ Basic "prim__integerToNat")
     then case constFold rho x of
            CPrimVal fc3 (BI v) =>
              if v >= 0 then CPrimVal fc3 (BI v) else CPrimVal fc3 (BI 0)
            v                   => CApp fc (CRef fc2 n) [v]
     else CApp fc (CRef fc2 n) [constFold rho x]
constFold rho (CApp fc x xs) = CApp fc (constFold rho x) (constFold rho <$> xs)
constFold rho (CCon fc x y tag xs) = CCon fc x y tag $ constFold rho <$> xs
constFold rho (COp {arity} fc fn xs) =
    let xs' = map (constFold rho) xs
        e = constRight fc fn xs'
     in fromMaybe e $ do
          guard (foldableOp fn)
          nfs <- traverse toNF xs'
          nf <- getOp fn nfs
          fromNF nf
  where
    toNF : CExp vars' -> Maybe (NF vars')
    -- Don't fold `Int` and `Double` because they have varying widths
    toNF (CPrimVal fc (I _)) = Nothing
    toNF (CPrimVal fc (Db _)) = Nothing
    -- Fold the rest
    toNF (CPrimVal fc c) = Just $ VPrimVal fc c
    toNF _ = Nothing

    fromNF : NF vars' -> Maybe (CExp vars')
    fromNF (VPrimVal fc c) = Just $ CPrimVal fc c
    fromNF _ = Nothing

    commutative : PrimType -> Bool
    commutative DoubleType = False
    commutative _ = True

    constRight : {ar : _} -> FC -> PrimFn ar ->
                 Vect ar (CExp vars') -> CExp vars'
    constRight fc (Add ty) [x@(CPrimVal _ _), y] =
        if commutative ty
            then COp fc (Add ty) [y, x]
            else COp fc (Add ty) [x, y]
    constRight fc (Mul ty) [x@(CPrimVal _ _), y] =
        if commutative ty
            then COp fc (Mul ty) [y, x]
            else COp fc (Mul ty) [x, y]
    constRight fc fn args = COp fc fn args

constFold rho (CExtPrim fc p xs) = CExtPrim fc p $ constFold rho <$> xs
constFold rho (CForce fc x y) = CForce fc x $ constFold rho y
constFold rho (CDelay fc x y) = CDelay fc x $ constFold rho y
constFold rho (CConCase fc sc xs x)
  = CConCase fc (constFold rho sc) (foldAlt rho <$> xs) (constFold rho <$> x)
  where
    foldScope : forall vars . {vars' : _} ->
                Subst vars vars' -> CCaseScope vars -> CCaseScope vars'
    foldScope rho (CRHS tm) = CRHS (constFold rho tm)
    foldScope rho (CArg x sc) = CArg x (foldScope (wk rho (mkSizeOf [<x])) sc)

    foldAlt : forall vars . {vars' : _} ->
              Subst vars vars' -> CConAlt vars -> CConAlt vars'
    foldAlt rho (MkConAlt n ci t sc)
        = MkConAlt n ci t (foldScope rho sc)

constFold rho (CConstCase fc sc xs x) =
    let sc' = constFold rho sc
     in case sc' of
        CPrimVal _ val => case findConstAlt val xs x of
            Just exp => constFold rho exp
            Nothing => CConstCase fc (constFold rho sc) (foldAlt <$> xs) (constFold rho <$> x)
        _ => CConstCase fc (constFold rho sc) (foldAlt <$> xs) (constFold rho <$> x)
  where
    foldAlt : CConstAlt vars -> CConstAlt vars'
    foldAlt (MkConstAlt c e) = MkConstAlt c $ constFold rho e
constFold rho (CPrimVal fc v) = CPrimVal fc v
constFold rho (CErased fc) = CErased fc
constFold rho (CCrash fc err) = CCrash fc err

constFoldCDef : CDef -> Maybe CDef
constFoldCDef (MkFun args exp)
  = Just $ MkFun args $ constFold (initSubst args) exp
constFoldCDef _ = Nothing

export
constantFold : Ref Ctxt Defs => Name -> Core ()
constantFold fn = do
    defs <- get Ctxt
    Just (fnIdx, gdef) <- lookupCtxtExactI fn defs.gamma
        | Nothing => pure ()
    let Just cdef = gdef.compexpr
        | Nothing => pure ()
    let Just cdef' = constFoldCDef cdef
        | Nothing => pure ()
    log "compiler.const-fold" 50 $ "constant folding " ++ show !(getFullName fn)
                                 ++ "\n\told def: " ++ show cdef
                                 ++ "\n\tnew def: " ++ show cdef'
    setCompiled (Resolved fnIdx) cdef'
