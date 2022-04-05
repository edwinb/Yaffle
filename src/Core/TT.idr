module Core.TT

import public Core.TT.TT

import Data.List
import Data.Nat

export
dropLater : IsVar nm (S idx) (v :: vs) -> IsVar nm idx vs
dropLater (Later p) = p

export
mkVar : (wkns : List Name) -> IsVar nm (length wkns) (wkns ++ nm :: vars)
mkVar [] = First
mkVar (w :: ws) = Later (mkVar ws)

public export
dropVar : (ns : List Name) -> {idx : Nat} -> (0 p : IsVar name idx ns) -> List Name
dropVar (n :: xs) First = xs
dropVar (n :: xs) (Later p) = n :: dropVar xs p

public export
data Var : List Name -> Type where
     MkVar : {i : Nat} -> (0 p : IsVar n i vars) -> Var vars

namespace Var

  export
  later : Var ns -> Var (n :: ns)
  later (MkVar p) = MkVar (Later p)

export
sameVar : Var xs -> Var xs -> Bool
sameVar (MkVar {i=x} _) (MkVar {i=y} _) = x == y

export
varIdx : Var xs -> Nat
varIdx (MkVar {i} _) = i

export
dropFirst : List (Var (v :: vs)) -> List (Var vs)
dropFirst [] = []
dropFirst (MkVar First :: vs) = dropFirst vs
dropFirst (MkVar (Later p) :: vs) = MkVar p :: dropFirst vs

export
Show (Var ns) where
  show (MkVar {i} _) = show i

namespace HasLength

  public export
  data HasLength : Nat -> List a -> Type where
    Z : HasLength Z []
    S : HasLength n as -> HasLength (S n) (a :: as)

  export
  sucR : HasLength n xs -> HasLength (S n) (xs ++ [x])
  sucR Z     = S Z
  sucR (S n) = S (sucR n)

  export
  hlAppend : HasLength m xs -> HasLength n ys -> HasLength (m + n) (xs ++ ys)
  hlAppend Z ys = ys
  hlAppend (S xs) ys = S (hlAppend xs ys)

  export
  mkHasLength : (xs : List a) -> HasLength (length xs) xs
  mkHasLength [] = Z
  mkHasLength (_ :: xs) = S (mkHasLength xs)

  export
  take : (n : Nat) -> (xs : Stream a) -> HasLength n (take n xs)
  take Z _ = Z
  take (S n) (x :: xs) = S (take n xs)

  export
  cast : {ys : _} -> List.length xs = List.length ys -> HasLength m xs -> HasLength m ys
  cast {ys = []}      eq Z = Z
  cast {ys = y :: ys} eq (S p) = S (cast (succInjective _ _ eq) p)
    where
    succInjective : (0 l, r : Nat) -> S l = S r -> l = r
    succInjective _ _ Refl = Refl

  hlReverseOnto : HasLength m acc -> HasLength n xs -> HasLength (m + n) (reverseOnto acc xs)
  hlReverseOnto p Z = rewrite plusZeroRightNeutral m in p
  hlReverseOnto {n = S n} p (S q) = rewrite sym (plusSuccRightSucc m n) in hlReverseOnto (S p) q

  export
  hlReverse : HasLength m acc -> HasLength m (reverse acc)
  hlReverse = hlReverseOnto Z

public export
record SizeOf {a : Type} (xs : List a) where
  constructor MkSizeOf
  size        : Nat
  0 hasLength : HasLength size xs

namespace SizeOf

  export
  0 theList : SizeOf {a} xs -> List a
  theList _ = xs

  export
  zero : SizeOf []
  zero = MkSizeOf Z Z

  export
  suc : SizeOf as -> SizeOf (a :: as)
  suc (MkSizeOf n p) = MkSizeOf (S n) (S p)

  -- ||| suc but from the right
  export
  sucR : SizeOf as -> SizeOf (as ++ [a])
  sucR (MkSizeOf n p) = MkSizeOf (S n) (sucR p)

  export
  (+) : SizeOf xs -> SizeOf ys -> SizeOf (xs ++ ys)
  MkSizeOf m p + MkSizeOf n q = MkSizeOf (m + n) (hlAppend p q)

  export
  mkSizeOf : (xs : List a) -> SizeOf xs
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

namespace CList
  -- A list correspoding to another list
  public export
  data CList : List a -> Type -> Type where
       Nil : CList [] ty
       (::) : (x : ty) -> CList cs ty -> CList (c :: cs) ty

public export
interface Weaken tm where
  weaken : {0 vars : List Name} -> tm vars -> tm (n :: vars)
  weakenNs : SizeOf ns -> tm vars -> tm (ns ++ vars)

  weakenNs p t = case sizedView p of
    Z   => t
    S p => weaken (weakenNs p t)

  weaken = weakenNs (suc zero)

public export
data NVar : Name -> List Name -> Type where
     MkNVar : {i : Nat} -> (0 p : IsVar n i vars) -> NVar n vars

namespace NVar
  export
  later : NVar nm ns -> NVar nm (n :: ns)
  later (MkNVar p) = MkNVar (Later p)

export
weakenNVar : SizeOf ns -> NVar name inner -> NVar name (ns ++ inner)
weakenNVar p x = case sizedView p of
  Z     => x
  (S p) => later (weakenNVar p x)

export
insertNVar : SizeOf outer ->
             NVar nm (outer ++ inner) ->
             NVar nm (outer ++ n :: inner)
insertNVar p v = case sizedView p of
  Z     => later v
  (S p) => case v of
    MkNVar First     => MkNVar First
    MkNVar (Later v) => later (insertNVar p (MkNVar v))

export
insertVar : SizeOf outer ->
            Var (outer ++ inner) ->
            Var (outer ++ n :: inner)
insertVar p (MkVar v) = let MkNVar v' = insertNVar p (MkNVar v) in MkVar v'


||| The (partial) inverse to insertVar
export
removeVar : SizeOf outer ->
            Var        (outer ++ [x] ++ inner) ->
            Maybe (Var (outer        ++ inner))
removeVar out var = case sizedView out of
  Z => case var of
          MkVar First     => Nothing
          MkVar (Later p) => Just (MkVar p)
  S out' => case var of
              MkVar First     => Just (MkVar First)
              MkVar (Later p) => later <$> removeVar out' (MkVar p)

export
weakenVar : SizeOf ns -> Var inner -> Var (ns ++ inner)
weakenVar p (MkVar v) = let MkNVar v' = weakenNVar p (MkNVar v) in MkVar v'

export
insertNVarNames : SizeOf outer -> SizeOf ns ->
                  NVar name (outer ++ inner) ->
                  NVar name (outer ++ (ns ++ inner))
insertNVarNames p q v = case sizedView p of
  Z     => weakenNVar q v
  (S p) => case v of
    MkNVar First      => MkNVar First
    MkNVar (Later v') => later (insertNVarNames p q (MkNVar v'))

export
insertVarNames : SizeOf outer -> SizeOf ns ->
                 Var (outer ++ inner) ->
                 Var (outer ++ (ns ++ inner))
insertVarNames p q (MkVar v) = let MkNVar v' = insertNVarNames p q (MkNVar v) in MkVar v'

public export
data SubVars : List Name -> List Name -> Type where
     SubRefl  : SubVars xs xs
     DropCons : SubVars xs ys -> SubVars xs (y :: ys)
     KeepCons : SubVars xs ys -> SubVars (x :: xs) (x :: ys)

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
subExtend : (ns : List Name) -> SubVars xs ys -> SubVars (ns ++ xs) (ns ++ ys)
subExtend [] sub = sub
subExtend (x :: xs) sub = KeepCons (subExtend xs sub)

export
subInclude : (ns : List Name) -> SubVars xs ys -> SubVars (xs ++ ns) (ys ++ ns)
subInclude ns SubRefl = SubRefl
subInclude ns (DropCons p) = DropCons (subInclude ns p)
subInclude ns (KeepCons p) = KeepCons (subInclude ns p)

namespace Bounds
  public export
  data Bounds : List Name -> Type where
       None : Bounds []
       Add : (x : Name) -> Name -> Bounds xs -> Bounds (x :: xs)

  export
  sizeOf : Bounds xs -> SizeOf xs
  sizeOf None        = zero
  sizeOf (Add _ _ b) = suc (sizeOf b)

export
addVars : SizeOf outer -> Bounds bound ->
          NVar name (outer ++ vars) ->
          NVar name (outer ++ (bound ++ vars))
addVars p = insertNVarNames p . sizeOf

export
Weaken Term where
  weakenNs = ?foo

-- Build a simple function type
export
fnType : {vars : _} -> FC -> Term vars -> Term vars -> Term vars
fnType fc arg scope = Bind emptyFC (MN "_" 0) (Pi fc top Explicit arg) (weaken scope)

export
linFnType : {vars : _} -> FC -> Term vars -> Term vars -> Term vars
linFnType fc arg scope = Bind emptyFC (MN "_" 0) (Pi fc linear Explicit arg) (weaken scope)

export
embed : Term vars -> Term (vars ++ more)
embed tm = believe_me tm

export
{vars : _} -> Show (Term vars) where
  show tm = ?todo_showtm
