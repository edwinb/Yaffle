module Core.TT

import public Core.TT.TT

import Data.List
import Data.Nat
import Data.SnocList
import Data.SnocList.Operations
import Data.Vect

import Libraries.Data.LengthMatch
import Libraries.Data.NameMap

%default covering

-- Check equality, ignoring variable naming and universes
export
total
eqTerm : Term vs -> Term vs' -> Bool
eqTerm (Local _ _ idx _) (Local _ _ idx' _) = idx == idx'
eqTerm (Ref _ _ n) (Ref _ _ n') = n == n'
eqTerm (Meta _ _ i args) (Meta _ _ i' args')
    = i == i' && assert_total
         (all (uncurry eqTerm) (zip (map snd args) (map snd args')))
eqTerm (Bind _ _ b sc) (Bind _ _ b' sc')
    = assert_total (eqBinderBy eqTerm b b') && eqTerm sc sc'
eqTerm (App _ f _ a) (App _ f' _ a') = eqTerm f f' && eqTerm a a'
eqTerm (As _ _ a p) (As _ _ a' p') = eqTerm p p'
eqTerm (Case _ _ sc ty alts) (Case _ _ sc' ty' alts')
    = eqTerm sc sc' && eqTerm ty ty' &&
          assert_total (all (uncurry eqAlt) (zip alts alts'))
  where
    eqScope : forall vs, vs' . CaseScope vs -> CaseScope vs' -> Bool
    eqScope (RHS tm) (RHS tm') = eqTerm tm tm'
    eqScope (Arg _ _ sc) (Arg _ _ sc') = eqScope sc sc'
    eqScope _ _ = False

    eqAlt : CaseAlt vs -> CaseAlt vs' -> Bool
    eqAlt (ConCase _ n tag sc) (ConCase _ n' tag' sc') = tag == tag' && eqScope sc sc'
    eqAlt (DelayCase _ ty arg tm) (DelayCase _ ty' arg' tm') = eqTerm tm tm'
    eqAlt (ConstCase _ c tm) (ConstCase _ c' tm') = c == c' && eqTerm tm tm'
    eqAlt (DefaultCase _ tm) (DefaultCase _ tm') = eqTerm tm tm'
    eqAlt _ _ = False
eqTerm (TDelayed _ _ t) (TDelayed _ _ t') = eqTerm t t'
eqTerm (TDelay _ _ t x) (TDelay _ _ t' x') = eqTerm t t' && eqTerm x x'
eqTerm (TForce _ _ t) (TForce _ _ t') = eqTerm t t'
eqTerm (PrimVal _ c) (PrimVal _ c') = c == c'
eqTerm (Erased _ i) (Erased _ i') = eqErased i i'
  where
    eqErased : WhyErased (Term vs) -> WhyErased (Term vs') -> Bool
    eqErased Placeholder Placeholder = True
    eqErased Impossible Impossible = True
    eqErased (Dotted x) (Dotted y) = eqTerm x y
    eqErased _ _ = False
eqTerm (Unmatched _ _) (Unmatched _ _) = True
eqTerm (TType _ _) (TType _ _) = True
eqTerm _ _ = False

export
Eq (Term vars) where
  (==) = eqTerm

public export
revOnto : (xs, vs : SnocList a) -> reverseOnto xs vs = xs ++ reverse vs
revOnto xs [<] = Refl
revOnto xs (vs :< v)
    = rewrite revOnto (xs :< v) vs in
        rewrite revOnto [<v] vs in
          rewrite appendAssociative xs [<v] (reverse vs) in Refl

public export
revNs : (vs, ns : SnocList a) -> reverse vs ++ reverse ns = reverse (ns ++ vs)
revNs [<] ns = rewrite appendLinLeftNeutral (reverse ns) in Refl
revNs (vs :< v) ns
    = rewrite revOnto [<v] vs in
        rewrite revOnto [<v] (ns ++ vs) in
          rewrite sym $ revNs vs ns in
            rewrite appendAssociative [<v] (reverse vs) (reverse ns) in Refl

public export
take : (n : Nat) -> (xs : Stream a) -> SnocList a
take Z xs = [<]
take (S k) (x :: xs) = take k xs :< x

public export
lengthMap : (xs : SnocList a) -> length (map f xs) = length xs
lengthMap [<] = Refl
lengthMap (sx :< x) = cong S (lengthMap sx)

export
dropLater : IsVar nm (S idx) (vs :< v) -> IsVar nm idx vs
dropLater (Later p) = p

export
mkVar : (wkns : SnocList Name) -> IsVar nm (length wkns) (vars :< nm ++ wkns) -- (wkns ++ nm :: vars)
mkVar [<] = First
mkVar (ws :< w) = Later (mkVar ws)

public export
dropVar : (ns : SnocList Name) -> {idx : Nat} -> (0 p : IsVar name idx ns) -> SnocList Name
dropVar (xs :< n) First = xs
dropVar (xs :< n) (Later p) = dropVar xs p :< n

public export
data Var : SnocList Name -> Type where
     MkVar : {i : Nat} -> (0 p : IsVar n i vars) -> Var vars

namespace Var

  export
  later : Var ns -> Var (ns :< n)
  later (MkVar p) = MkVar (Later p)

export
sameVar : Var xs -> Var xs -> Bool
sameVar (MkVar {i=x} _) (MkVar {i=y} _) = x == y

export
varIdx : Var xs -> Nat
varIdx (MkVar {i} _) = i

export
dropFirst : SnocList (Var (vs :< v)) -> SnocList (Var vs)
dropFirst [<] = [<]
dropFirst (vs :< MkVar First) = dropFirst vs
dropFirst (vs :< MkVar (Later p)) = dropFirst vs :< MkVar p

export
Show (Var ns) where
  show (MkVar {i} _) = show i

namespace HasLength

  public export
  data HasLength : Nat -> SnocList a -> Type where
    Z : HasLength Z [<]
    S : HasLength n as -> HasLength (S n) (as :< a)

  export
  sucR : HasLength n xs -> HasLength (S n) (cons x xs)
  sucR Z     = S Z
  sucR (S n) = S (sucR n)

  export
  hlAppend : HasLength m xs -> HasLength n ys -> HasLength (m + n) (ys ++ xs)
  hlAppend Z ys = ys
  hlAppend (S xs) ys = S (hlAppend xs ys)

  export
  mkHasLength : (xs : SnocList a) -> HasLength (length xs) xs
  mkHasLength [<] = Z
  mkHasLength (xs :< _) = S (mkHasLength xs)

  export
  take : (n : Nat) -> (xs : Stream a) -> HasLength n (take n xs)
  take Z _ = Z
  take (S n) (x :: xs) = S (take n xs)

  export
  cast : {ys : _} -> SnocList.length xs = SnocList.length ys -> HasLength m xs -> HasLength m ys
  cast {ys = [<]}     eq Z = Z
  cast {ys = ys :< y} eq (S p) = S (cast (inj _ eq) p)

  hlReverseOnto : HasLength m acc -> HasLength n xs -> HasLength (m + n) (reverseOnto acc xs)
  hlReverseOnto p Z = rewrite plusZeroRightNeutral m in p
  hlReverseOnto {n = S n} p (S q) = rewrite sym (plusSuccRightSucc m n) in hlReverseOnto (S p) q

  export
  hlReverse : HasLength m acc -> HasLength m (reverse acc)
  hlReverse = hlReverseOnto Z


public export
record SizeOf {a : Type} (xs : SnocList a) where
  constructor MkSizeOf
  size        : Nat
  0 hasLength : HasLength size xs

namespace SizeOf

  export
  0 theSnocList : SizeOf {a} xs -> SnocList a
  theSnocList _ = xs

  export
  zero : SizeOf [<]
  zero = MkSizeOf Z Z

  export
  suc : SizeOf as -> SizeOf (as :< a)
  suc (MkSizeOf n p) = MkSizeOf (S n) (S p)

  -- ||| suc but from the right
  export
  sucR : SizeOf as -> SizeOf (cons a as)
  sucR (MkSizeOf n p) = MkSizeOf (S n) (sucR p)

  export
  (+) : SizeOf xs -> SizeOf ys -> SizeOf (ys ++ xs)
  MkSizeOf m p + MkSizeOf n q = MkSizeOf (m + n) (hlAppend p q)

  export
  mkSizeOf : (xs : SnocList a) -> SizeOf xs
  mkSizeOf xs = MkSizeOf (length xs) (mkHasLength xs)

  export
  reverse : SizeOf xs -> SizeOf (reverse xs)
  reverse (MkSizeOf n p) = MkSizeOf n (hlReverse p)

  export
  map : SizeOf xs -> SizeOf (map f xs)
  map (MkSizeOf n p) = MkSizeOf n (cast (sym $ lengthMap xs) p)

  export
  take : {n : Nat} -> {0 xs : Stream a} -> SizeOf (take n xs)
  take = MkSizeOf n (take n xs)

namespace SizedView

  public export
  data SizedView : SizeOf as -> Type where
    Z : SizedView (MkSizeOf Z Z)
    S : (n : SizeOf as) -> SizedView (suc {a} n)

export
sizedView : (p : SizeOf as) -> SizedView p
sizedView (MkSizeOf Z Z)         = Z
sizedView (MkSizeOf (S n) (S p)) = S (MkSizeOf n p)

namespace CSnocList
  -- A list correspoding to another list
  public export
  data CSnocList : SnocList a -> Type -> Type where
       Nil : CSnocList [<] ty
       (::) : (x : ty) -> CSnocList cs ty -> CSnocList (cs :< c) ty

public export
interface Weaken tm where
  weaken : {0 vars : SnocList Name} -> tm vars -> tm (vars :< n)
  weakenNs : SizeOf ns -> tm vars -> tm (vars ++ ns)

  weakenNs p t = case sizedView p of
    Z   => t
    S p => weaken (weakenNs p t)

  weaken = weakenNs (suc zero)

public export
data NVar : Name -> SnocList Name -> Type where
     MkNVar : {i : Nat} -> (0 p : IsVar n i vars) -> NVar n vars

namespace NVar
  export
  later : NVar nm ns -> NVar nm (ns :< n)
  later (MkNVar p) = MkNVar (Later p)

export
weakenNVar : SizeOf ns -> NVar name inner -> NVar name (inner ++ ns)
weakenNVar p x = case sizedView p of
  Z     => x
  (S p) => later (weakenNVar p x)

export
insertNVar : SizeOf outer ->
             NVar nm (inner ++ outer) ->
             NVar nm (inner :< n ++ outer)
insertNVar p v = case sizedView p of
  Z     => later v
  (S p) => case v of
    MkNVar First     => MkNVar First
    MkNVar (Later v) => later (insertNVar p (MkNVar v))

export
insertVar : SizeOf outer ->
            Var (inner ++ outer) ->
            Var (inner :< n ++ outer)
insertVar p (MkVar v) = let MkNVar v' = insertNVar p (MkNVar v) in MkVar v'


||| The (partial) inverse to insertVar
export
removeVar : SizeOf outer ->
            Var        (inner :< x ++ outer) ->
            Maybe (Var (inner ++ outer))
removeVar out var = case sizedView out of
  Z => case var of
          MkVar First     => Nothing
          MkVar (Later p) => Just (MkVar p)
  S out' => case var of
              MkVar First     => Just (MkVar First)
              MkVar (Later p) => later <$> removeVar out' (MkVar p)

export
weakenVar : SizeOf ns -> Var inner -> Var (inner ++ ns)
weakenVar p (MkVar v) = let MkNVar v' = weakenNVar p (MkNVar v) in MkVar v'

export
insertNVarNames : SizeOf outer -> SizeOf ns ->
                  NVar name (inner ++ outer) ->
                  NVar name (inner ++ ns ++ outer)
insertNVarNames p q v = case sizedView p of
  Z     => weakenNVar q v
  (S p) => case v of
    MkNVar First      => MkNVar First
    MkNVar (Later v') => later (insertNVarNames p q (MkNVar v'))

export
insertVarNames : SizeOf outer -> SizeOf ns ->
                 Var (inner ++ outer) ->
                 Var (inner ++ ns ++ outer)
insertVarNames p q (MkVar v) = let MkNVar v' = insertNVarNames p q (MkNVar v) in MkVar v'

insertNamesAlt : SizeOf outer -> SizeOf ns ->
                 CaseAlt (inner ++ outer) ->
                 CaseAlt (inner ++ ns ++ outer)

export
insertNames : SizeOf outer -> SizeOf ns ->
              Term (inner ++ outer) ->
              Term (inner ++ ns ++ outer)
insertNames out ns (Local fc r idx prf)
   = let MkNVar prf' = insertNVarNames out ns (MkNVar prf) in
         Local fc r _ prf'
insertNames out ns (Ref fc nt name)
    = Ref fc nt name
insertNames out ns (Meta fc x y xs)
    = Meta fc x y (map (\ (q, tm) => (q, insertNames out ns tm)) xs)
insertNames out ns (Bind fc x b scope)
    = Bind fc x (map (insertNames out ns) b)
           (insertNames (suc out) ns scope)
insertNames out ns (App fc fn q arg)
    = App fc (insertNames out ns fn) q (insertNames out ns arg)
insertNames out sns (As fc x as pat)
    = As fc x (insertAs as) (insertNames out sns pat)
  where
    insertAs : AsName (inner ++ outer) -> AsName (inner ++ ns ++ outer)
    insertAs (AsLoc fc idx prf)
        = let MkNVar prf' = insertNVarNames out sns (MkNVar prf) in
              AsLoc fc _ prf'
    insertAs (AsRef fc n) = AsRef fc n
insertNames out ns (Case fc r sc scTy xs)
    = Case fc r (insertNames out ns sc) (insertNames out ns scTy)
           (map (insertNamesAlt out ns) xs)
insertNames out ns (TDelayed fc x y)
    = TDelayed fc x (insertNames out ns y)
insertNames out ns (TDelay fc x ty arg)
    = TDelay fc x (insertNames out ns ty) (insertNames out ns arg)
insertNames out ns (TForce fc x y)
    = TForce fc x (insertNames out ns y)
insertNames out ns (PrimVal fc c) = PrimVal fc c
insertNames out ns (PrimOp fc x xs)
    = PrimOp fc x (map (insertNames out ns) xs)
insertNames out ns (Erased fc why) = Erased fc (insertNames out ns <$> why)
insertNames out ns (Unmatched fc x) = Unmatched fc x
insertNames out ns (TType fc u) = TType fc u

insertNamesScope : forall outer . SizeOf outer -> SizeOf ns ->
              CaseScope (inner ++ outer) ->
              CaseScope (inner ++ ns ++ outer)
insertNamesScope out ns (RHS tm) = RHS (insertNames out ns tm)
insertNamesScope out ns (Arg r x sc)
    = Arg r x (insertNamesScope (suc out) ns sc)

-- Declared above, mutual with insertNames
-- insertNamesAlt : SizeOf outer -> SizeOf ns ->
--                  CaseAlt (outer ++ inner) ->
--                  CaseAlt (outer ++ (ns ++ inner))
insertNamesAlt out sns (ConCase fc n t scope)
    = ConCase fc n t (insertNamesScope out sns scope)
insertNamesAlt out ns (DelayCase fc ty arg scope)
    = DelayCase fc ty arg (insertNames (suc (suc out)) ns scope)
insertNamesAlt out ns (ConstCase fc c scope)
    = ConstCase fc c (insertNames out ns scope)
insertNamesAlt out ns (DefaultCase fc scope)
    = DefaultCase fc (insertNames out ns scope)

public export
data SubVars : SnocList Name -> SnocList Name -> Type where
     SubRefl  : SubVars xs xs
     DropCons : SubVars xs ys -> SubVars xs (ys :< y)
     KeepCons : SubVars xs ys -> SubVars (xs :< x) (ys :< x)

export
subElem : {idx : Nat} -> (0 p : IsVar name idx xs) ->
          SubVars ys xs -> Maybe (Var ys)
subElem prf SubRefl = Just (MkVar prf)
subElem First (DropCons p) = Nothing
subElem (Later x) (DropCons p)
    = do MkVar prf' <- subElem x p
         Just (MkVar prf')
subElem First (KeepCons p) = Just (MkVar First)
subElem (Later x) (KeepCons p)
    = do MkVar prf' <- subElem x p
         Just (MkVar (Later prf'))

export
subExtend : (ns : SnocList Name) -> SubVars xs ys -> SubVars (xs ++ ns) (ys ++ ns)
subExtend [<] sub = sub
subExtend (xs :< _) sub = KeepCons (subExtend xs sub)

export
subInclude : (ns : SnocList Name) -> SubVars xs ys -> SubVars (ns ++ xs) (ns ++ ys)
subInclude ns SubRefl = SubRefl
subInclude ns (DropCons p) = DropCons (subInclude ns p)
subInclude ns (KeepCons p) = KeepCons (subInclude ns p)

export
shrinkTerm : Term vars -> SubVars newvars vars -> Maybe (Term newvars)
export
shrinkPi : PiInfo (Term vars) -> SubVars newvars vars ->
           Maybe (PiInfo (Term newvars))
export
shrinkBinder : Binder (Term vars) -> SubVars newvars vars ->
               Maybe (Binder (Term newvars))
shrinkAs : AsName vars -> SubVars newvars vars -> Maybe (AsName newvars)
shrinkScope : CaseScope vars -> SubVars newvars vars -> Maybe (CaseScope newvars)
shrinkAlt : CaseAlt vars -> SubVars newvars vars -> Maybe (CaseAlt newvars)

shrinkPi Explicit prf = pure Explicit
shrinkPi Implicit prf = pure Implicit
shrinkPi AutoImplicit prf = pure AutoImplicit
shrinkPi (DefImplicit t) prf = pure (DefImplicit !(shrinkTerm t prf))

shrinkBinder (Lam fc c p ty) prf
    = Just (Lam fc c !(shrinkPi p prf) !(shrinkTerm ty prf))
shrinkBinder (Let fc c val ty) prf
    = Just (Let fc c !(shrinkTerm val prf) !(shrinkTerm ty prf))
shrinkBinder (Pi fc c p ty) prf
    = Just (Pi fc c !(shrinkPi p prf) !(shrinkTerm ty prf))
shrinkBinder (PVar fc c p ty) prf
    = Just (PVar fc c !(shrinkPi p prf) !(shrinkTerm ty prf))
shrinkBinder (PLet fc c val ty) prf
    = Just (PLet fc c !(shrinkTerm val prf) !(shrinkTerm ty prf))
shrinkBinder (PVTy fc c ty) prf
    = Just (PVTy fc c !(shrinkTerm ty prf))

shrinkAs (AsLoc fc idx loc) prf = (\(MkVar loc') => AsLoc fc _ loc') <$> subElem loc prf
shrinkAs (AsRef fc n) prf = Just (AsRef fc n)

shrinkScope (RHS tm) prf = Just (RHS !(shrinkTerm tm prf))
shrinkScope (Arg r x sc) prf = Just (Arg r x !(shrinkScope sc (KeepCons prf)))

shrinkAlt (ConCase fc x tag sc) prf
    = Just (ConCase fc x tag !(shrinkScope sc prf))
shrinkAlt (DelayCase fc ty arg sc) prf
    = Just (DelayCase fc ty arg !(shrinkTerm sc (KeepCons (KeepCons prf))))
shrinkAlt (ConstCase fc c sc) prf = Just (ConstCase fc c !(shrinkTerm sc prf))
shrinkAlt (DefaultCase fc sc) prf = Just (DefaultCase fc !(shrinkTerm sc prf))

shrinkTerm (Local fc r idx loc) prf = (\(MkVar loc') => Local fc r _ loc') <$> subElem loc prf
shrinkTerm (Ref fc x name) prf = Just (Ref fc x name)
shrinkTerm (Meta fc x y xs) prf
   = do xs' <- traverse (\ (q, tm) => do tm' <- shrinkTerm tm prf
                                         pure (q, tm')) xs
        Just (Meta fc x y xs')
shrinkTerm (Bind fc x b scope) prf
   = Just (Bind fc x !(shrinkBinder b prf) !(shrinkTerm scope (KeepCons prf)))
shrinkTerm (App fc fn q arg) prf
   = Just (App fc !(shrinkTerm fn prf) q !(shrinkTerm arg prf))
shrinkTerm (As fc s as tm) prf
   = Just (As fc s !(shrinkAs as prf) !(shrinkTerm tm prf))
shrinkTerm (Case fc r sc scTy alts) prf
   = Just (Case fc r !(shrinkTerm sc prf) !(shrinkTerm scTy prf)
                !(traverse (\alt => shrinkAlt alt prf) alts))
shrinkTerm (TDelayed fc x y) prf
   = Just (TDelayed fc x !(shrinkTerm y prf))
shrinkTerm (TDelay fc x t y) prf
   = Just (TDelay fc x !(shrinkTerm t prf) !(shrinkTerm y prf))
shrinkTerm (TForce fc r x) prf
   = Just (TForce fc r !(shrinkTerm x prf))
shrinkTerm (PrimVal fc c) prf = Just (PrimVal fc c)
shrinkTerm (PrimOp fc fn args) prf
   = Just (PrimOp fc fn !(traverse (\arg => shrinkTerm arg prf) args))
shrinkTerm (Erased fc why) prf = Erased fc <$> traverse (`shrinkTerm` prf) why
shrinkTerm (Unmatched fc s) prf = Just (Unmatched fc s)
shrinkTerm (TType fc u) prf = Just (TType fc u)

namespace Bounds
  public export
  data Bounds : SnocList Name -> Type where
       None : Bounds [<]
       Add : (x : Name) -> Name -> Bounds xs -> Bounds (xs :< x)

  export
  sizeOf : Bounds xs -> SizeOf xs
  sizeOf None        = zero
  sizeOf (Add _ _ b) = suc (sizeOf b)

export
addVars : SizeOf outer -> Bounds bound ->
          NVar name (vars ++ outer) ->
          NVar name (vars ++ bound ++ outer)
addVars p = insertNVarNames p . sizeOf

resolveRef : SizeOf outer -> SizeOf done -> Bounds bound -> FC -> Name ->
             Maybe (Term (vars ++ (bound ++ done) ++ outer))
resolveRef p q None fc n = Nothing
resolveRef {outer} {done} p q (Add {xs} new old bs) fc n
    = if n == old
         then let MkNVar p = weakenNVar (p + q) (MkNVar First) in
                  Just (Local fc Nothing _
                   (rewrite sym $ appendAssociative (xs :< new) done outer in
                    rewrite appendAssociative vars (xs :< new) (done ++ outer) in p))
         else rewrite sym $ appendAssociative xs [<new] done in
                      resolveRef p (sucR q) bs fc n

mkLocalsAs : SizeOf outer -> Bounds bound ->
             AsName (vars ++ outer) -> AsName (vars ++ (bound ++ outer))
mkLocalsAs outer bs (AsLoc fc idx p)
    = let MkNVar p' = addVars outer bs (MkNVar p) in AsLoc fc _ p'
mkLocalsAs outer bs (AsRef fc n)
    = case resolveRef outer zero bs fc n of
           Just (Local fc _ _ p) => AsLoc fc _ p
           _ => AsRef fc n

mkLocalsAlt : SizeOf outer -> Bounds bound ->
              CaseAlt (vars ++ outer) -> CaseAlt (vars ++ (bound ++ outer))

mkLocals : SizeOf outer -> Bounds bound ->
           Term (vars ++ outer) -> Term (vars ++ (bound ++ outer))
mkLocals outer bs (Local fc r idx p)
    = let MkNVar p' = addVars outer bs (MkNVar p) in Local fc r _ p'
mkLocals outer bs (Ref fc Bound name)
    = maybe (Ref fc Bound name) id (resolveRef outer zero bs fc name)
mkLocals outer bs (Ref fc nt name)
    = Ref fc nt name
mkLocals outer bs (Meta fc name y xs)
    = maybe (Meta fc name y (map (\ (q, tm) => (q, mkLocals outer bs tm)) xs))
            id (resolveRef outer zero bs fc name)
mkLocals outer bs (Bind fc x b scope)
    = Bind fc x (map (mkLocals outer bs) b)
           (mkLocals (suc outer) bs scope)
mkLocals outer bs (App fc fn q arg)
    = App fc (mkLocals outer bs fn) q (mkLocals outer bs arg)
mkLocals outer bs (As fc s as tm)
    = As fc s (mkLocalsAs outer bs as) (mkLocals outer bs tm)
mkLocals outer bs (Case fc r sc scTy alts)
    = Case fc r (mkLocals outer bs sc) (mkLocals outer bs scTy)
           (map (mkLocalsAlt outer bs) alts)
mkLocals outer bs (TDelayed fc x y)
    = TDelayed fc x (mkLocals outer bs y)
mkLocals outer bs (TDelay fc x t y)
    = TDelay fc x (mkLocals outer bs t) (mkLocals outer bs y)
mkLocals outer bs (TForce fc r x)
    = TForce fc r (mkLocals outer bs x)
mkLocals outer bs (PrimVal fc c) = PrimVal fc c
mkLocals outer bs (PrimOp fc fn args)
    = PrimOp fc fn (map (mkLocals outer bs) args)
mkLocals outer bs (Erased fc why) = Erased fc (mkLocals outer bs <$> why)
mkLocals outer bs (Unmatched fc s) = Unmatched fc s
mkLocals outer bs (TType fc u) = TType fc u

mkLocalsCaseScope
    : SizeOf outer -> Bounds bound ->
      CaseScope (vars ++ outer) -> CaseScope (vars ++ (bound ++ outer))
mkLocalsCaseScope outer bs (RHS tm) = RHS (mkLocals outer bs tm)
mkLocalsCaseScope outer bs (Arg r x scope)
    = Arg r x (mkLocalsCaseScope (suc outer) bs scope)

mkLocalsAlt outer bs (ConCase fc n t scope)
    = ConCase fc n t (mkLocalsCaseScope outer bs scope)
mkLocalsAlt outer bs (DelayCase fc ty arg rhs)
    = DelayCase fc ty arg (mkLocals (suc (suc outer)) bs rhs)
mkLocalsAlt outer bs (ConstCase fc c rhs) = ConstCase fc c (mkLocals outer bs rhs)
mkLocalsAlt outer bs (DefaultCase fc rhs) = DefaultCase fc (mkLocals outer bs rhs)

export
refsToLocals : Bounds bound -> Term vars -> Term (vars ++ bound)
refsToLocals None y = y
refsToLocals bs y = mkLocals zero  bs y

export
refsToLocalsCaseScope : Bounds bound -> CaseScope vars -> CaseScope (vars ++ bound)
refsToLocalsCaseScope bs sc = mkLocalsCaseScope zero bs sc

-- Replace any reference to 'x' with a locally bound name 'new'
export
refToLocal : (x : Name) -> (new : Name) -> Term vars -> Term (vars :< new)
refToLocal x new tm = refsToLocals (Add new x None) tm

export
isNVar : (n : Name) -> (ns : SnocList Name) -> Maybe (NVar n ns)
isNVar n [<] = Nothing
isNVar n (ms :< m)
    = case nameEq n m of
           Nothing   => map later (isNVar n ms)
           Just Refl => pure (MkNVar First)

export
isVar : (n : Name) -> (ns : SnocList Name) -> Maybe (Var ns)
isVar n ns = do
  MkNVar v <- isNVar n ns
  pure (MkVar v)

-- Replace any Ref Bound in a type with appropriate local
export
resolveNames : (vars : SnocList Name) -> Term vars -> Term vars
resolveNames vars (Ref fc Bound name)
    = case isNVar name vars of
           Just (MkNVar prf) => Local fc (Just False) _ prf
           _ => Ref fc Bound name
resolveNames vars (Meta fc n i xs)
    = Meta fc n i (map (\ (c, t) => (c, resolveNames vars t)) xs)
resolveNames vars (Bind fc x b scope)
    = Bind fc x (map (resolveNames vars) b) (resolveNames (vars :< x) scope)
resolveNames vars (App fc fn c arg)
    = App fc (resolveNames vars fn) c (resolveNames vars arg)
resolveNames vars (As fc s v@(AsLoc{}) pat)
    = As fc s v (resolveNames vars pat)
resolveNames vars (Case fc c sc scty alts)
    = Case fc c (resolveNames vars sc) (resolveNames vars scty)
                (map (resolveAlt vars) alts)
  where
    resolveScope : (vars : SnocList Name) -> CaseScope vars -> CaseScope vars
    resolveScope vars (RHS tm) = RHS (resolveNames vars tm)
    resolveScope vars (Arg c x sc) = Arg c x (resolveScope (vars :< x) sc)

    resolveAlt : (vars : SnocList Name) -> CaseAlt vars -> CaseAlt vars
    resolveAlt vars (ConCase fc x tag sc)
        = ConCase fc x tag (resolveScope vars sc)
    resolveAlt vars (DelayCase fc ty arg tm)
        = DelayCase fc ty arg (resolveNames (vars :< arg :< ty) tm)
    resolveAlt vars (ConstCase fc x tm) = ConstCase fc x (resolveNames vars tm)
    resolveAlt vars (DefaultCase fc tm) = DefaultCase fc (resolveNames vars tm)

resolveNames vars (As fc s v@(AsRef afc name) pat)
    = case isNVar name vars of
           Just (MkNVar prf) => As fc s (AsLoc afc _ prf) (resolveNames vars pat)
           _ => As fc s v (resolveNames vars pat)
resolveNames vars (TDelayed fc x y)
    = TDelayed fc x (resolveNames vars y)
resolveNames vars (TDelay fc x t y)
    = TDelay fc x (resolveNames vars t) (resolveNames vars y)
resolveNames vars (TForce fc r x)
    = TForce fc r (resolveNames vars x)
resolveNames vars (PrimOp fc fn args)
    = PrimOp fc fn (map (resolveNames vars) args)
resolveNames vars tm = tm

export
Weaken Term where
  weakenNs p tm = insertNames zero p tm

export
Weaken CaseScope where
  weakenNs p sc = insertNamesScope zero p sc

export
Weaken CaseAlt where
  weakenNs p sc = insertNamesAlt zero p sc

export
apply : FC -> Term vars -> List (RigCount, Term vars) -> Term vars
apply loc fn [] = fn
apply loc fn ((q, a) :: args) = apply loc (App loc fn q a) args

export
applySpine : FC -> Term vars -> SnocList (RigCount, Term vars) -> Term vars
applySpine loc fn [<] = fn
applySpine loc fn (args :< (q, a)) = App loc (applySpine loc fn args) q a

-- Creates a chain of `App` nodes, each with its own file context
export
applyWithFC : Term vars -> List (FC, RigCount, Term vars) -> Term vars
applyWithFC fn [] = fn
applyWithFC fn ((fc, q, arg) :: args) = applyWithFC (App fc fn q arg) args

-- Build a simple function type
export
fnType : {vars : _} -> FC -> Term vars -> Term vars -> Term vars
fnType fc arg scope = Bind emptyFC (MN "_" 0) (Pi fc top Explicit arg) (weaken scope)

export
linFnType : {vars : _} -> FC -> Term vars -> Term vars -> Term vars
linFnType fc arg scope = Bind emptyFC (MN "_" 0) (Pi fc linear Explicit arg) (weaken scope)

export
getFnArgs : Term vars -> (Term vars, List (Term vars))
getFnArgs tm = getFA [] tm
  where
    getFA : List (Term vars) -> Term vars ->
            (Term vars, List (Term vars))
    getFA args (App _ f _ a) = getFA (a :: args) f
    getFA args tm = (tm, args)

export
getFnArgsSpine : Term vars -> (Term vars, SnocList (RigCount, Term vars))
getFnArgsSpine (App _ f c a)
    = let (fn, sp) = getFnArgsSpine f in
          (fn, sp :< (c, a))
getFnArgsSpine tm = (tm, [<])

export
getFn : Term vars -> Term vars
getFn (App _ f _ a) = getFn f
getFn tm = tm

export
getArgs : Term vars -> (List (Term vars))
getArgs = snd . getFnArgs

export
Weaken Var where
  weaken = later

export
varExtend : IsVar x idx xs -> IsVar x idx (ys ++ xs)
-- What Could Possibly Go Wrong?
-- This relies on the runtime representation of the term being the same
-- after embedding! It is just an identity function at run time, though, and
-- we don't need its definition at compile time, so let's do it...
varExtend p = believe_me p

export
embed : Term vars -> Term (more ++ vars)
embed tm = believe_me tm

export
renameNTop : (ms : SnocList Name) ->
             LengthMatch ns ms ->
             Term (vars ++ ns) -> Term (vars ++ ms)
renameNTop ms ok tm = believe_me tm

export
renameVars : (ms : SnocList Name) ->
             LengthMatch ns ms ->
             Term ns -> Term ms
renameVars ms ok tm = believe_me tm

export
renameTop : (m : Name) -> Term (vars :< n) -> Term (vars :< m)
renameTop m tm = renameNTop {ns = [<n]} [<m] (SnocMatch LinMatch) tm

export
nameAt : {vars : _} -> {idx : Nat} -> (0 p : IsVar n idx vars) -> Name
nameAt {vars = ns :< n} First     = n
nameAt {vars = ns :< n} (Later p) = nameAt p

-- Substitute some explicit terms for names in a term, and remove those
-- names from the scope
namespace SubstEnv
  public export
  data SubstEnv : SnocList Name -> SnocList Name -> Type where
       Lin : SubstEnv [<] vars
       (:<) : SubstEnv ds vars -> Term vars -> SubstEnv (ds :< d) vars

  findDrop : FC -> Maybe Bool ->
             Var (vars ++ dropped) ->
             SubstEnv dropped vars ->
             Term vars
  findDrop fc r (MkVar var) [<] = Local fc r _ var
  findDrop fc r (MkVar First) (env :< tm) = tm
  findDrop fc r (MkVar (Later p)) (env :< tm)
      = findDrop fc r (MkVar p) env

  find : FC -> Maybe Bool ->
         SizeOf outer ->
         Var ((vars ++ dropped) ++ outer) ->
         SubstEnv dropped vars ->
         Term (vars ++ outer)
  find fc r outer var env = case sizedView outer of
    Z       => findDrop fc r var env
    S outer => case var of
      MkVar First     => Local fc r _ First
      MkVar (Later p) => weaken (find fc r outer (MkVar p) env)
       -- TODO: refactor to only weaken once?

  substAlt : SizeOf outer ->
             SubstEnv dropped vars ->
             CaseAlt ((vars ++ dropped) ++ outer) ->
             CaseAlt (vars ++ outer)

  substEnv : SizeOf outer ->
             SubstEnv dropped vars ->
             Term ((vars ++ dropped) ++ outer) ->
             Term (vars ++ outer)
  substEnv outer env (Local fc r _ prf)
      = find fc r outer (MkVar prf) env
  substEnv outer env (Ref fc x name) = Ref fc x name
  substEnv outer env (Meta fc n i xs)
      = Meta fc n i (map (\ (c, t) => (c, substEnv outer env t)) xs)
  substEnv outer env (Bind fc x b scope)
      = Bind fc x (map (substEnv outer env) b)
                  (substEnv (suc outer) env scope)
  substEnv outer env (App fc fn c arg)
      = App fc (substEnv outer env fn) c (substEnv outer env arg)
  substEnv outer env (As fc s (AsLoc afc _ prf) pat)
      -- Doesn't make sense if the local is resolved!
      = case find fc Nothing outer (MkVar prf) env of
             Local fc _ _ prf' =>
                 As fc s (AsLoc afc _ prf') (substEnv outer env pat)
             _ => substEnv outer env pat
  substEnv outer env (As fc s (AsRef afc n) pat)
      = As fc s (AsRef afc n) (substEnv outer env pat)
  substEnv outer env (Case fc c sc scty alts)
      = Case fc c (substEnv outer env sc)
             (substEnv outer env scty)
             (map (substAlt outer env) alts)
  substEnv outer env (TDelayed fc x y) = TDelayed fc x (substEnv outer env y)
  substEnv outer env (TDelay fc x t y)
      = TDelay fc x (substEnv outer env t) (substEnv outer env y)
  substEnv outer env (TForce fc r x) = TForce fc r (substEnv outer env x)
  substEnv outer env (PrimVal fc c) = PrimVal fc c
  substEnv outer env (PrimOp fc op args) = ?todoPrimOp
  substEnv outer env (Erased fc i) = Erased fc (substEnv outer env <$> i)
  substEnv outer env (Unmatched fc str) = Unmatched fc str
  substEnv outer env (TType fc u) = TType fc u

  substCaseScope : SizeOf outer ->
             SubstEnv dropped vars ->
             CaseScope ((vars ++ dropped) ++ outer) ->
             CaseScope (vars ++ outer)
  substCaseScope outer env (RHS tm) = RHS (substEnv outer env tm)
  substCaseScope outer env (Arg c x sc)
      = Arg c x (substCaseScope (suc outer) env sc)

  substAlt outer env (ConCase fc n t sc)
      = ConCase fc n t (substCaseScope outer env sc)
  substAlt outer env (DelayCase fc ty arg sc)
      = DelayCase fc ty arg (substEnv (suc (suc outer)) env sc)
  substAlt outer env (ConstCase fc c sc)
      = ConstCase fc c (substEnv outer env sc)
  substAlt outer env (DefaultCase fc sc)
      = DefaultCase fc (substEnv outer env sc)

  export
  substs : SubstEnv dropped vars -> Term (vars ++ dropped) -> Term vars
  substs env tm = substEnv zero env tm

  export
  subst : Term vars -> Term (vars :< x) -> Term vars
  subst val tm = substs [<val] tm

-- Replace an explicit name with a term
export
substName : Name -> Term vars -> Term vars -> Term vars
substName x new (Ref fc nt name)
    = case nameEq x name of
           Nothing => Ref fc nt name
           Just Refl => new
substName x new (Meta fc n i xs)
    = Meta fc n i (map (\ (c, t) => (c, substName x new t)) xs)
-- ASSUMPTION: When we substitute under binders, the name has always been
-- resolved to a Local, so no need to check that x isn't shadowing
substName x new (Bind fc y b scope)
    = Bind fc y (map (substName x new) b) (substName x (weaken new) scope)
substName x new (App fc fn c arg)
    = App fc (substName x new fn) c (substName x new arg)
substName x new (As fc s as pat)
    = As fc s as (substName x new pat)
substName x new (Case fc c sc scty alts)
    = Case fc c (substName x new sc) (substName x new scty)
           (map (substNameAlt new) alts)
  where
    substNameScope : forall vars . Term vars -> CaseScope vars -> CaseScope vars
    substNameScope new (RHS tm) = RHS (substName x new tm)
    substNameScope new (Arg c n sc)
        = Arg c n (substNameScope (weaken new) sc)

    substNameAlt : forall vars . Term vars -> CaseAlt vars -> CaseAlt vars
    substNameAlt new (ConCase cfc n t sc)
        = ConCase cfc n t (substNameScope new sc)
    substNameAlt new (DelayCase fc ty arg rhs)
        = DelayCase fc ty arg (substName x (weakenNs (suc (suc zero)) new) rhs)
    substNameAlt new (ConstCase fc c tm) = ConstCase fc c (substName x new tm)
    substNameAlt new (DefaultCase fc tm) = DefaultCase fc (substName x new tm)
substName x new (TDelayed fc y z)
    = TDelayed fc y (substName x new z)
substName x new (TDelay fc y t z)
    = TDelay fc y (substName x new t) (substName x new z)
substName x new (TForce fc r y)
    = TForce fc r (substName x new y)
substName x new (PrimOp fc fn args)
    = PrimOp fc fn (map (substName x new) args)
substName x new tm = tm

-- Replace a bound variable with a term
export
substVar : Var vars -> (new : Term vars) -> Term vars -> Term vars
substVar (MkVar {i} p) new loc@(Local fc m idx p')
    = if i == idx
         then new
         else loc
substVar x new (Meta fc n i xs)
    = Meta fc n i (map (\ (c, t) => (c, substVar x new t)) xs)
substVar x new (Bind fc y b scope)
    = Bind fc y (map (substVar x new) b)
                (substVar (weaken x) (weaken new) scope)
substVar x new (App fc fn c arg)
    = App fc (substVar x new fn) c (substVar x new arg)
substVar x new (As fc s as pat)
    = As fc s as (substVar x new pat)
substVar x new (Case fc c sc scty alts)
    = Case fc c (substVar x new sc) (substVar x new scty)
           (map (substVarAlt x new) alts)
  where
    substVarScope : forall vars . Var vars -> Term vars -> CaseScope vars -> CaseScope vars
    substVarScope x new (RHS tm) = RHS (substVar x new tm)
    substVarScope x new (Arg c n sc)
        = Arg c n (substVarScope (weaken x) (weaken new) sc)
--
    substVarAlt : forall vars . Var vars -> Term vars -> CaseAlt vars -> CaseAlt vars
    substVarAlt x new (ConCase cfc n t sc)
        = ConCase cfc n t (substVarScope x new sc)
    substVarAlt x new (DelayCase fc ty arg rhs)
        = DelayCase fc ty arg
                    (substVar (weakenNs (suc (suc zero)) x)
                              (weakenNs (suc (suc zero)) new) rhs)
    substVarAlt x new (ConstCase fc c tm) = ConstCase fc c (substVar x new tm)
    substVarAlt x new (DefaultCase fc tm) = DefaultCase fc (substVar x new tm)
substVar x new (TDelayed fc y z)
    = TDelayed fc y (substVar x new z)
substVar x new (TDelay fc y t z)
    = TDelay fc y (substVar x new t) (substVar x new z)
substVar x new (TForce fc r y)
    = TForce fc r (substVar x new y)
substVar x new (PrimOp fc fn args)
    = PrimOp fc fn (map (substVar x new) args)
substVar x new tm = tm

export
addMetas : (usingResolved : Bool) -> NameMap Bool -> Term vars -> NameMap Bool
addMetas res ns (Local fc x idx y) = ns
addMetas res ns (Ref fc x name) = ns
addMetas res ns (Meta fc n i xs)
  = addMetaArgs (insert (ifThenElse res (Resolved i) n) False ns) (map snd xs)
  where
    addMetaArgs : NameMap Bool -> List (Term vars) -> NameMap Bool
    addMetaArgs ns [] = ns
    addMetaArgs ns (t :: ts) = addMetaArgs (addMetas res ns t) ts
addMetas res ns (Bind fc x (Let _ c val ty) scope)
    = addMetas res (addMetas res (addMetas res ns val) ty) scope
addMetas res ns (Bind fc x b scope)
    = addMetas res (addMetas res ns (binderType b)) scope
addMetas res ns (App fc fn c arg)
    = addMetas res (addMetas res ns fn) arg
addMetas res ns (As fc s as tm) = addMetas res ns tm
addMetas res ns (Case fc c sc scty alts)
    = addMetaAlts (addMetas res (addMetas res ns sc) scty) alts
  where
    addMetaScope : forall vars . NameMap Bool -> CaseScope vars -> NameMap Bool
    addMetaScope ns (RHS tm) = addMetas res ns tm
    addMetaScope ns (Arg c x sc) = addMetaScope ns sc

    addMetaAlt : NameMap Bool -> CaseAlt vars -> NameMap Bool
    addMetaAlt ns (ConCase fc n t sc) = addMetaScope ns sc
    addMetaAlt ns (DelayCase fc ty arg tm) = addMetas res ns tm
    addMetaAlt ns (ConstCase fc c tm) = addMetas res ns tm
    addMetaAlt ns (DefaultCase fc tm) = addMetas res ns tm

    addMetaAlts : NameMap Bool -> List (CaseAlt vars) -> NameMap Bool
    addMetaAlts ns [] = ns
    addMetaAlts ns (t :: ts) = addMetaAlts (addMetaAlt ns t) ts
addMetas res ns (TDelayed fc x y) = addMetas res ns y
addMetas res ns (TDelay fc x t y)
    = addMetas res (addMetas res ns t) y
addMetas res ns (TForce fc r x) = addMetas res ns x
addMetas res ns (PrimVal fc c) = ns
addMetas res ns (PrimOp fc op args) = addMetaArgs ns args
  where
    addMetaArgs : NameMap Bool -> Vect n (Term vars) -> NameMap Bool
    addMetaArgs ns [] = ns
    addMetaArgs ns (t :: ts) = addMetaArgs (addMetas res ns t) ts
addMetas res ns (Erased fc i) = ns
addMetas res ns (Unmatched fc str) = ns
addMetas res ns (TType fc u) = ns

-- Get the metavariable names in a term
export
getMetas : Term vars -> NameMap Bool
getMetas tm = addMetas False empty tm

export
addRefs : (underAssert : Bool) -> (aTotal : Name) ->
          NameMap Bool -> Term vars -> NameMap Bool
addRefs ua at ns (Local fc x idx y) = ns
addRefs ua at ns (Ref fc x name) = insert name ua ns
addRefs ua at ns (Meta fc n i xs) = addRefArgs ns (map snd xs)
  where
    addRefArgs : NameMap Bool -> List (Term vars) -> NameMap Bool
    addRefArgs ns [] = ns
    addRefArgs ns (t :: ts) = addRefArgs (addRefs ua at ns t) ts
addRefs ua at ns (Bind fc x (Let _ c val ty) scope)
    = addRefs ua at (addRefs ua at (addRefs ua at ns val) ty) scope
addRefs ua at ns (Bind fc x b scope)
    = addRefs ua at (addRefs ua at ns (binderType b)) scope
addRefs ua at ns (App _ (App _ (Ref fc _ name) _ x) _ y)
    = if name == at
         then addRefs True at (insert name True ns) y
         else addRefs ua at (addRefs ua at (insert name ua ns) x) y
addRefs ua at ns (App fc fn c arg)
    = addRefs ua at (addRefs ua at ns fn) arg
addRefs ua at ns (As fc s as tm) = addRefs ua at ns tm
addRefs ua at ns (Case fc c sc scty alts)
    = addRefAlts (addRefs ua at (addRefs ua at ns sc) scty) alts
  where
    addRefScope : forall vars . NameMap Bool -> CaseScope vars -> NameMap Bool
    addRefScope ns (RHS tm) = addRefs ua at ns tm
    addRefScope ns (Arg c x sc) = addRefScope ns sc

    addRefAlt : NameMap Bool -> CaseAlt vars -> NameMap Bool
    addRefAlt ns (ConCase fc n t sc) = addRefScope ns sc
    addRefAlt ns (DelayCase fc ty arg tm) = addRefs ua at ns tm
    addRefAlt ns (ConstCase fc c tm) = addRefs ua at ns tm
    addRefAlt ns (DefaultCase fc tm) = addRefs ua at ns tm

    addRefAlts : NameMap Bool -> List (CaseAlt vars) -> NameMap Bool
    addRefAlts ns [] = ns
    addRefAlts ns (t :: ts) = addRefAlts (addRefAlt ns t) ts
addRefs ua at ns (TDelayed fc x y) = addRefs ua at ns y
addRefs ua at ns (TDelay fc x t y)
    = addRefs ua at (addRefs ua at ns t) y
addRefs ua at ns (TForce fc r x) = addRefs ua at ns x
addRefs ua at ns (PrimVal fc c) = ns
addRefs ua at ns (PrimOp fc op args) = addRefArgs ns args
  where
    addRefArgs : NameMap Bool -> Vect n (Term vars) -> NameMap Bool
    addRefArgs ns [] = ns
    addRefArgs ns (t :: ts) = addRefArgs (addRefs ua at ns t) ts
addRefs ua at ns (Erased fc i) = ns
addRefs ua at ns (Unmatched fc str) = ns
addRefs ua at ns (TType fc u) = ns

-- As above, but for references. Also flag whether a name is under an
-- 'assert_total' because we may need to know that in coverage/totality
-- checking
export
getRefs : (aTotal : Name) -> Term vars -> NameMap Bool
getRefs at tm = addRefs False at empty tm

{vars : _} -> Show (AsName vars) where
  show (AsLoc _ _ p) = show (nameAt p)
  show (AsRef _ n) = show n

export
withPiInfo : Show t => PiInfo t -> String -> String
withPiInfo Explicit tm = "(" ++ tm ++ ")"
withPiInfo Implicit tm = "{" ++ tm ++ "}"
withPiInfo AutoImplicit tm = "{auto " ++ tm ++ "}"
withPiInfo (DefImplicit t) tm = "{default " ++ show t ++ " " ++ tm ++ "}"

mutual
  export
  {vars : _} -> Show (Term vars) where
    show tm = let (fn, args) = getFnArgs tm in assert_total (showApp fn args)
      where
        -- TODO: There's missing cases here, and the assert_total above
        -- shouldn't be necessary, so fix that!
        showApp : {vars : _} -> Term vars -> List (Term vars) -> String
        showApp (Local _ c idx p) []
           = show (nameAt p) ++ "[" ++ show idx ++ "]"
        showApp (Ref _ _ n) [] = show n
        showApp (Meta _ n _ args) []
            = "?" ++ show n ++ "_" ++ show args
        showApp (Bind _ x (Lam _ c info ty) sc) []
            = "\\" ++ withPiInfo info (show c ++ show x ++ " : " ++ show ty) ++
              " => " ++ show sc
        showApp (Bind _ x (Let _ c val ty) sc) []
            = "let " ++ show c ++ show x ++ " : " ++ show ty ++
              " = " ++ show val ++ " in " ++ show sc
        showApp (Bind _ x (Pi _ c info ty) sc) []
            = "(" ++ withPiInfo info (show c ++ show x ++ " : " ++ show ty) ++
              " -> " ++ show sc ++ ")"
        showApp (Bind _ x (PVar _ c info ty) sc) []
            = withPiInfo info ("pat " ++ show c ++ show x ++ " : " ++ show ty) ++
              " => " ++ show sc
        showApp (Bind _ x (PLet _ c val ty) sc) []
            = "plet " ++ show c ++ show x ++ " : " ++ show ty ++
              " = " ++ show val ++ " in " ++ show sc
        showApp (Bind _ x (PVTy _ c ty) sc) []
            = "pty " ++ show c ++ show x ++ " : " ++ show ty ++
              " => " ++ show sc
        showApp (App _ _ _ _) [] = "[can't happen]"
        showApp (As _ _ n tm) [] = show n ++ "@" ++ show tm
        showApp (Case _ _ sc _ alts) []
            = "case " ++ show sc ++ " of " ++ show alts
        showApp (TDelayed _ _ tm) [] = "%Delayed " ++ show tm
        showApp (TDelay _ _ _ tm) [] = "%Delay " ++ show tm
        showApp (TForce _ _ tm) [] = "%Force " ++ show tm
        showApp (PrimVal _ c) [] = show c
        showApp (PrimOp _ op args) [] = show op ++ show args
        showApp (Erased _ Placeholder) [] = "[__]"
        showApp (Erased _ Impossible) [] = "impossible"
        showApp (Erased _ (Dotted t)) [] = ".(\{showApp t []})"
        showApp (Unmatched _ str) [] = "Unmatched: " ++ show str
        showApp (TType _ u) [] = "Type"
        showApp f args@(_ :: _)
          = "(" ++ assert_total (show f) ++ " " ++
             assert_total (showSep " " (map show args))
             ++ ")"

  export
  {vars : _} -> Show (CaseScope vars) where
      show (RHS rhs) = " => " ++ show rhs
      show (Arg r nm sc) = " " ++ show nm ++ show sc

  export
  {vars : _} -> Show (CaseAlt vars) where
     show (ConCase fc n t sc) = show n ++ show sc
     show (DelayCase fc ty arg sc) = "Delay " ++ show arg ++ " => " ++ show sc
     show (ConstCase fc c sc) = show c ++ " => " ++ show sc
     show (DefaultCase fc sc) = "_ => " ++ show sc
