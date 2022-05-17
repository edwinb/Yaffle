module Core.TT

import public Core.TT.TT

import Data.SnocList
import Data.SnocList.Operations
import Data.Nat
import Data.Vect

public export
reverseOnto : SnocList a -> SnocList a -> SnocList a
reverseOnto acc [<] = acc
reverseOnto acc (sx :< x) = reverseOnto (acc :< x) sx

public export
reverse : SnocList a -> SnocList a
reverse = reverseOnto [<]

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
dropFirst : List (Var (vs :< v)) -> List (Var vs)
dropFirst [] = []
dropFirst (MkVar First :: vs) = dropFirst vs
dropFirst (MkVar (Later p) :: vs) = MkVar p :: dropFirst vs

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
    = Meta fc x y (map (insertNames out ns) xs)
insertNames out ns (Bind fc x b scope)
    = Bind fc x (map (insertNames out ns) b)
           (insertNames (suc out) ns scope)
insertNames out ns (App fc fn arg)
    = App fc (insertNames out ns fn) (insertNames out ns arg)
insertNames out sns (As fc x as pat)
    = As fc x (insertAs as) (insertNames out sns pat)
  where
    insertAs : AsName (inner ++ outer) -> AsName (inner ++ ns ++ outer)
    insertAs (AsLoc fc idx prf)
        = let MkNVar prf' = insertNVarNames out sns (MkNVar prf) in
              AsLoc fc _ prf'
    insertAs (AsRef fc n) = AsRef fc n
insertNames out ns (Case fc sc scTy xs)
    = Case fc (insertNames out ns sc) (insertNames out ns scTy)
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
insertNames out ns (Erased fc imp) = Erased fc imp
insertNames out ns (Unmatched fc x) = Unmatched fc x
insertNames out ns (Impossible fc) = Impossible fc
insertNames out ns (TType fc u) = TType fc u

-- Declared above, mutual with insertNames
-- insertNamesAlt : SizeOf outer -> SizeOf ns ->
--                  CaseAlt (outer ++ inner) ->
--                  CaseAlt (outer ++ (ns ++ inner))
insertNamesAlt out sns (ConCase n t scope)
    = ConCase n t (insertScope out sns scope)
  where
    insertScope : forall outer . SizeOf outer -> SizeOf ns ->
                  CaseScope (inner ++ outer) ->
                  CaseScope (inner ++ ns ++ outer)
    insertScope out ns (RHS tm) = RHS (insertNames out ns tm)
    insertScope out ns (Arg x sc)
        = Arg x (insertScope (suc out) ns sc)
insertNamesAlt out ns (DelayCase ty arg scope)
    = DelayCase ty arg (insertNames (suc (suc out)) ns scope)
insertNamesAlt out ns (ConstCase c scope)
    = ConstCase c (insertNames out ns scope)
insertNamesAlt out ns (DefaultCase scope)
    = DefaultCase (insertNames out ns scope)

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
shrinkPi : PiInfo (Term vars) -> SubVars newvars vars ->
           Maybe (PiInfo (Term newvars))
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
shrinkScope (Arg x sc) prf = Just (Arg x !(shrinkScope sc (KeepCons prf)))

shrinkAlt (ConCase x tag sc) prf
    = Just (ConCase x tag !(shrinkScope sc prf))
shrinkAlt (DelayCase ty arg sc) prf
    = Just (DelayCase ty arg !(shrinkTerm sc (KeepCons (KeepCons prf))))
shrinkAlt (ConstCase c sc) prf = Just (ConstCase c !(shrinkTerm sc prf))
shrinkAlt (DefaultCase sc) prf = Just (DefaultCase !(shrinkTerm sc prf))

shrinkTerm (Local fc r idx loc) prf = (\(MkVar loc') => Local fc r _ loc') <$> subElem loc prf
shrinkTerm (Ref fc x name) prf = Just (Ref fc x name)
shrinkTerm (Meta fc x y xs) prf
   = do xs' <- traverse (\x => shrinkTerm x prf) xs
        Just (Meta fc x y xs')
shrinkTerm (Bind fc x b scope) prf
   = Just (Bind fc x !(shrinkBinder b prf) !(shrinkTerm scope (KeepCons prf)))
shrinkTerm (App fc fn arg) prf
   = Just (App fc !(shrinkTerm fn prf) !(shrinkTerm arg prf))
shrinkTerm (As fc s as tm) prf
   = Just (As fc s !(shrinkAs as prf) !(shrinkTerm tm prf))
shrinkTerm (Case fc sc scTy alts) prf
   = Just (Case fc !(shrinkTerm sc prf) !(shrinkTerm scTy prf)
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
shrinkTerm (Erased fc i) prf = Just (Erased fc i)
shrinkTerm (Unmatched fc s) prf = Just (Unmatched fc s)
shrinkTerm (Impossible fc) prf = Just (Impossible fc)
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
    = maybe (Meta fc name y (map (mkLocals outer bs) xs))
            id (resolveRef outer zero bs fc name)
mkLocals outer bs (Bind fc x b scope)
    = Bind fc x (map (mkLocals outer bs) b)
           (mkLocals (suc outer) bs scope)
mkLocals outer bs (App fc fn arg)
    = App fc (mkLocals outer bs fn) (mkLocals outer bs arg)
mkLocals outer bs (As fc s as tm)
    = As fc s (mkLocalsAs outer bs as) (mkLocals outer bs tm)
mkLocals outer bs (Case fc sc scTy alts)
    = Case fc (mkLocals outer bs sc) (mkLocals outer bs scTy)
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
mkLocals outer bs (Erased fc i) = Erased fc i
mkLocals outer bs (Unmatched fc s) = Unmatched fc s
mkLocals outer bs (Impossible fc) = Impossible fc
mkLocals outer bs (TType fc u) = TType fc u

mkLocalsCaseScope
    : SizeOf outer -> Bounds bound ->
      CaseScope (vars ++ outer) -> CaseScope (vars ++ (bound ++ outer))
mkLocalsCaseScope outer bs (RHS tm) = RHS (mkLocals outer bs tm)
mkLocalsCaseScope outer bs (Arg x scope)
    = Arg x (mkLocalsCaseScope (suc outer) bs scope)

mkLocalsAlt outer bs (ConCase n t scope)
    = ConCase n t (mkLocalsCaseScope outer bs scope)
mkLocalsAlt outer bs (DelayCase ty arg rhs)
    = DelayCase ty arg (mkLocals (suc (suc outer)) bs rhs)
mkLocalsAlt outer bs (ConstCase c rhs) = ConstCase c (mkLocals outer bs rhs)
mkLocalsAlt outer bs (DefaultCase rhs) = DefaultCase (mkLocals outer bs rhs)

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
Weaken Term where
  weakenNs p tm = insertNames zero p tm

export
apply : FC -> Term vars -> List (Term vars) -> Term vars
apply loc fn [] = fn
apply loc fn (a :: args) = apply loc (App loc fn a) args

-- Creates a chain of `App` nodes, each with its own file context
export
applyWithFC : Term vars -> List (FC, Term vars) -> Term vars
applyWithFC fn [] = fn
applyWithFC fn ((fc, arg) :: args) = applyWithFC (App fc fn arg) args

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
    getFA args (App _ f a) = getFA (a :: args) f
    getFA args tm = (tm, args)

export
getFn : Term vars -> Term vars
getFn (App _ f a) = getFn f
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
renameTop : (m : Name) -> Term (vars :< n) -> Term (vars :< m)
renameTop m tm = believe_me tm

export
nameAt : {vars : _} -> {idx : Nat} -> (0 p : IsVar n idx vars) -> Name
nameAt {vars = ns :< n} First     = n
nameAt {vars = ns :< n} (Later p) = nameAt p

export
withPiInfo : Show t => PiInfo t -> String -> String
withPiInfo Explicit tm = "(" ++ tm ++ ")"
withPiInfo Implicit tm = "{" ++ tm ++ "}"
withPiInfo AutoImplicit tm = "{auto " ++ tm ++ "}"
withPiInfo (DefImplicit t) tm = "{default " ++ show t ++ " " ++ tm ++ "}"

{vars : _} -> Show (AsName vars) where
  show (AsLoc _ _ p) = show (nameAt p)
  show (AsRef _ n) = show n

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
        showApp (App _ _ _) [] = "[can't happen]"
        showApp (As _ _ n tm) [] = show n ++ "@" ++ show tm
        showApp (Case _ sc _ alts) []
            = "case " ++ show sc ++ " of " ++ show alts
        showApp (TDelayed _ _ tm) [] = "%Delayed " ++ show tm
        showApp (TDelay _ _ _ tm) [] = "%Delay " ++ show tm
        showApp (TForce _ _ tm) [] = "%Force " ++ show tm
        showApp (PrimVal _ c) [] = show c
        showApp (PrimOp _ op args) [] = show op ++ show args
        showApp (Erased _ _) [] = "[__]"
        showApp (Unmatched _ str) [] = "Unmatched: " ++ show str
        showApp (Impossible _) [] = "impossible"
        showApp (TType _ u) [] = "Type"
        showApp _ [] = "???"
        showApp f args = "(" ++ assert_total (show f) ++ " " ++
                          assert_total (showSep " " (map show args))
                       ++ ")"

  export
  {vars : _} -> Show (CaseAlt vars) where
     show (ConCase n t sc) = "???"
     show (DelayCase ty arg sc) = "???"
     show (ConstCase c sc) = show c ++ " => " ++ show sc
     show (DefaultCase sc) = "_ => " ++ show sc
