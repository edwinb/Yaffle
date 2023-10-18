module Core.TT.TT

import public Core.FC
import public Core.TT.Name
import public Core.TT.RigCount

import Data.String
import Data.Vect
import Decidable.Equality
import Libraries.Data.Primitives
import Libraries.Data.String.Extra
import Libraries.Text.PrettyPrint.Prettyprinter
import Libraries.Text.PrettyPrint.Prettyprinter.Util

public export
Tag : Type
Tag = Int

public export
data NameType : Type where
     Bound   : NameType
     Func    : NameType
     DataCon : (tag : Tag) -> (arity : Nat) -> NameType
     TyCon   : (arity : Nat) -> NameType

export
covering
Show NameType where
  showPrec d Bound = "Bound"
  showPrec d Func = "Func"
  showPrec d (DataCon tag ar) = showCon d "DataCon" $ showArg tag ++ showArg ar
  showPrec d (TyCon ar) = showCon d "TyCon" $ showArg ar

export
isCon : NameType -> Maybe (Int, Nat)
isCon (DataCon t a) = Just (t, a)
isCon (TyCon a) = Just (-1, a)
isCon _ = Nothing

public export
data PrimType
    = IntType
    | Int8Type
    | Int16Type
    | Int32Type
    | Int64Type
    | IntegerType
    | Bits8Type
    | Bits16Type
    | Bits32Type
    | Bits64Type
    | StringType
    | CharType
    | DoubleType
    | WorldType

%name PrimType pty

public export
data Constant =
      I Int
    | I8  Int8
    | I16 Int16
    | I32 Int32
    | I64 Int64
    | BI  Integer
    | B8  Bits8
    | B16 Bits16
    | B32 Bits32
    | B64 Bits64

    | Str String
    | Ch Char
    | Db Double
    | PrT PrimType
    | WorldVal

export
isConstantType : Name -> Maybe PrimType
isConstantType (UN (Basic n)) = case n of
  "Int"     => Just IntType
  "Int8"    => Just Int8Type
  "Int16"   => Just Int16Type
  "Int32"   => Just Int32Type
  "Int64"   => Just Int64Type
  "Integer" => Just IntegerType
  "Bits8"   => Just Bits8Type
  "Bits16"  => Just Bits16Type
  "Bits32"  => Just Bits32Type
  "Bits64"  => Just Bits64Type
  "String"  => Just StringType
  "Char"    => Just CharType
  "Double"  => Just DoubleType
  "%World"  => Just WorldType
  _ => Nothing
isConstantType _ = Nothing

export
isPrimType : Constant -> Bool
isPrimType (PrT _) = True
isPrimType _       = False

export
primTypeEq : (x, y : PrimType) -> Maybe (x = y)
primTypeEq IntType IntType = Just Refl
primTypeEq Int8Type Int8Type = Just Refl
primTypeEq Int16Type Int16Type = Just Refl
primTypeEq Int32Type Int32Type = Just Refl
primTypeEq Int64Type Int64Type = Just Refl
primTypeEq IntegerType IntegerType = Just Refl
primTypeEq StringType StringType = Just Refl
primTypeEq CharType CharType = Just Refl
primTypeEq DoubleType DoubleType = Just Refl
primTypeEq WorldType WorldType = Just Refl
primTypeEq _ _ = Nothing

export
constantEq : (x, y : Constant) -> Maybe (x = y)
constantEq (I x) (I y) = case decEq x y of
                              Yes Refl => Just Refl
                              No contra => Nothing
constantEq (I8 x) (I8 y) = case decEq @{TempI8} x y of
                                  Yes Refl => Just Refl
                                  No contra => Nothing
constantEq (I16 x) (I16 y) = case decEq @{TempI16} x y of
                                  Yes Refl => Just Refl
                                  No contra => Nothing
constantEq (I32 x) (I32 y) = case decEq @{TempI32} x y of
                                  Yes Refl => Just Refl
                                  No contra => Nothing
constantEq (I64 x) (I64 y) = case decEq @{TempI64} x y of
                                  Yes Refl => Just Refl
                                  No contra => Nothing
constantEq (B8 x) (B8 y) = case decEq @{TempB8} x y of
                                  Yes Refl => Just Refl
                                  No contra => Nothing
constantEq (B16 x) (B16 y) = case decEq @{TempB16} x y of
                                  Yes Refl => Just Refl
                                  No contra => Nothing
constantEq (B32 x) (B32 y) = case decEq @{TempB32} x y of
                                  Yes Refl => Just Refl
                                  No contra => Nothing
constantEq (B64 x) (B64 y) = case decEq @{TempB64} x y of
                                  Yes Refl => Just Refl
                                  No contra => Nothing
constantEq (BI x) (BI y) = case decEq x y of
                                Yes Refl => Just Refl
                                No contra => Nothing
constantEq (Str x) (Str y) = case decEq x y of
                                  Yes Refl => Just Refl
                                  No contra => Nothing
constantEq (Ch x) (Ch y) = case decEq x y of
                                Yes Refl => Just Refl
                                No contra => Nothing
constantEq (Db x) (Db y) = Nothing -- no DecEq for Doubles!
constantEq (PrT x) (PrT y) = (\ eq => cong PrT eq) <$> primTypeEq x y
constantEq WorldVal WorldVal = Just Refl
constantEq _ _ = Nothing

export
Show PrimType where
  show IntType = "Int"
  show Int8Type = "Int8"
  show Int16Type = "Int16"
  show Int32Type = "Int32"
  show Int64Type = "Int64"
  show IntegerType = "Integer"
  show Bits8Type = "Bits8"
  show Bits16Type = "Bits16"
  show Bits32Type = "Bits32"
  show Bits64Type = "Bits64"
  show StringType = "String"
  show CharType = "Char"
  show DoubleType = "Double"
  show WorldType = "%World"

export
Show Constant where
  show (I x) = show x
  show (I8 x) = show x
  show (I16 x) = show x
  show (I32 x) = show x
  show (I64 x) = show x
  show (BI x) = show x
  show (B8 x) = show x
  show (B16 x) = show x
  show (B32 x) = show x
  show (B64 x) = show x
  show (Str x) = show x
  show (Ch x) = show x
  show (Db x) = show x
  show (PrT x) = show x
  show WorldVal = "%MkWorld"

Pretty ann PrimType where
  pretty c = case c of
    IntType => "Int"
    Int8Type => "Int8"
    Int16Type => "Int16"
    Int32Type => "Int32"
    Int64Type => "Int64"
    IntegerType => "Integer"
    Bits8Type => "Bits8"
    Bits16Type => "Bits16"
    Bits32Type => "Bits32"
    Bits64Type => "Bits64"
    StringType => "String"
    CharType => "Char"
    DoubleType => "Double"
    WorldType => "%World"

export
Eq PrimType where
  IntType == IntType = True
  Int8Type == Int8Type = True
  Int16Type == Int16Type = True
  Int32Type == Int32Type = True
  Int64Type == Int64Type = True
  IntegerType == IntegerType = True
  Bits8Type == Bits8Type = True
  Bits16Type == Bits16Type = True
  Bits32Type == Bits32Type = True
  Bits64Type == Bits64Type = True
  StringType == StringType = True
  CharType == CharType = True
  DoubleType == DoubleType = True
  WorldType == WorldType = True
  _ == _ = False

export
Eq Constant where
  (I x) == (I y) = x == y
  (I8 x) == (I8 y) = x == y
  (I16 x) == (I16 y) = x == y
  (I32 x) == (I32 y) = x == y
  (I64 x) == (I64 y) = x == y
  (BI x) == (BI y) = x == y
  (B8 x) == (B8 y) = x == y
  (B16 x) == (B16 y) = x == y
  (B32 x) == (B32 y) = x == y
  (B64 x) == (B64 y) = x == y
  (Str x) == (Str y) = x == y
  (Ch x) == (Ch y) = x == y
  (Db x) == (Db y) = x == y
  (PrT x) == (PrT y) = x == y
  WorldVal == WorldVal = True
  _ == _ = False

-- for typecase
export
primTypeTag : PrimType -> Int
-- 1 = ->, 2 = Type
primTypeTag IntType = 3
primTypeTag IntegerType = 4
primTypeTag Bits8Type = 5
primTypeTag Bits16Type = 6
primTypeTag Bits32Type = 7
primTypeTag Bits64Type = 8
primTypeTag StringType = 9
primTypeTag CharType = 10
primTypeTag DoubleType = 11
primTypeTag WorldType = 12
primTypeTag Int8Type = 13
primTypeTag Int16Type = 14
primTypeTag Int32Type = 15
primTypeTag Int64Type = 16

||| Precision of integral types.
public export
data Precision = P Int | Unlimited

export
Eq Precision where
  (P m) == (P n)         = m == n
  Unlimited == Unlimited = True
  _         == _         = False

export
Ord Precision where
  compare (P m) (P n)         = compare m n
  compare Unlimited Unlimited = EQ
  compare Unlimited _         = GT
  compare _         Unlimited = LT

-- so far, we only support limited precision
-- unsigned integers
public export
data IntKind = Signed Precision | Unsigned Int

public export
intKind : PrimType -> Maybe IntKind
intKind IntegerType = Just $ Signed Unlimited
intKind Int8Type    = Just . Signed   $ P 8
intKind Int16Type   = Just . Signed   $ P 16
intKind Int32Type   = Just . Signed   $ P 32
intKind Int64Type   = Just . Signed   $ P 64
intKind IntType     = Just . Signed   $ P 64
intKind Bits8Type   = Just $ Unsigned 8
intKind Bits16Type  = Just $ Unsigned 16
intKind Bits32Type  = Just $ Unsigned 32
intKind Bits64Type  = Just $ Unsigned 64
intKind _           = Nothing

public export
precision : IntKind -> Precision
precision (Signed p)   = p
precision (Unsigned p) = P p

-- All the internal operators, parameterised by their arity
public export
data PrimFn : Nat -> Type where
     Add : (ty : PrimType) -> PrimFn 2
     Sub : (ty : PrimType) -> PrimFn 2
     Mul : (ty : PrimType) -> PrimFn 2
     Div : (ty : PrimType) -> PrimFn 2
     Mod : (ty : PrimType) -> PrimFn 2
     Neg : (ty : PrimType) -> PrimFn 1
     ShiftL : (ty : PrimType) -> PrimFn 2
     ShiftR : (ty : PrimType) -> PrimFn 2

     BAnd : (ty : PrimType) -> PrimFn 2
     BOr : (ty : PrimType) -> PrimFn 2
     BXOr : (ty : PrimType) -> PrimFn 2

     LT  : (ty : PrimType) -> PrimFn 2
     LTE : (ty : PrimType) -> PrimFn 2
     EQ  : (ty : PrimType) -> PrimFn 2
     GTE : (ty : PrimType) -> PrimFn 2
     GT  : (ty : PrimType) -> PrimFn 2

     StrLength : PrimFn 1
     StrHead : PrimFn 1
     StrTail : PrimFn 1
     StrIndex : PrimFn 2
     StrCons : PrimFn 2
     StrAppend : PrimFn 2
     StrReverse : PrimFn 1
     StrSubstr : PrimFn 3

     DoubleExp : PrimFn 1
     DoubleLog : PrimFn 1
     DoublePow : PrimFn 2
     DoubleSin : PrimFn 1
     DoubleCos : PrimFn 1
     DoubleTan : PrimFn 1
     DoubleASin : PrimFn 1
     DoubleACos : PrimFn 1
     DoubleATan : PrimFn 1
     DoubleSqrt : PrimFn 1
     DoubleFloor : PrimFn 1
     DoubleCeiling : PrimFn 1

     Cast : PrimType -> PrimType -> PrimFn 1
     BelieveMe : PrimFn 3
     Crash : PrimFn 2

export
Show (PrimFn arity) where
  show (Add ty) = "+" ++ show ty
  show (Sub ty) = "-" ++ show ty
  show (Mul ty) = "*" ++ show ty
  show (Div ty) = "/" ++ show ty
  show (Mod ty) = "%" ++ show ty
  show (Neg ty) = "neg " ++ show ty
  show (ShiftL ty) = "shl " ++ show ty
  show (ShiftR ty) = "shr " ++ show ty
  show (BAnd ty) = "and " ++ show ty
  show (BOr ty) = "or " ++ show ty
  show (BXOr ty) = "xor " ++ show ty
  show (LT ty) = "<" ++ show ty
  show (LTE ty) = "<=" ++ show ty
  show (EQ ty) = "==" ++ show ty
  show (GTE ty) = ">=" ++ show ty
  show (GT ty) = ">" ++ show ty
  show StrLength = "op_strlen"
  show StrHead = "op_strhead"
  show StrTail = "op_strtail"
  show StrIndex = "op_strindex"
  show StrCons = "op_strcons"
  show StrAppend = "++"
  show StrReverse = "op_strrev"
  show StrSubstr = "op_strsubstr"
  show DoubleExp = "op_doubleExp"
  show DoubleLog = "op_doubleLog"
  show DoublePow = "op_doublePow"
  show DoubleSin = "op_doubleSin"
  show DoubleCos = "op_doubleCos"
  show DoubleTan = "op_doubleTan"
  show DoubleASin = "op_doubleASin"
  show DoubleACos = "op_doubleACos"
  show DoubleATan = "op_doubleATan"
  show DoubleSqrt = "op_doubleSqrt"
  show DoubleFloor = "op_doubleFloor"
  show DoubleCeiling = "op_doubleCeiling"
  show (Cast x y) = "cast-" ++ show x ++ "-" ++ show y
  show BelieveMe = "believe_me"
  show Crash = "crash"

export
sameFn : PrimFn x -> PrimFn y -> Bool
sameFn (Add _) (Add _) = True
sameFn (Sub _) (Sub _) = True
sameFn (Mul _) (Mul _)= True
sameFn (Div _) (Div _) = True
sameFn (Mod _) (Mod _) = True
sameFn (Neg _) (Neg _) = True
sameFn (ShiftL _) (ShiftL _) = True
sameFn (ShiftR _) (ShiftR _) = True
sameFn (BAnd _) (BAnd _) = True
sameFn (BOr _) (BOr _) = True
sameFn (BXOr _) (BXOr _) = True
sameFn (LT _) (LT _) = True
sameFn (LTE _) (LTE _) = True
sameFn (EQ _) (EQ _) = True
sameFn (GTE _) (GTE _) = True
sameFn (GT _) (GT _) = True
sameFn StrLength StrLength = True
sameFn StrHead StrHead = True
sameFn StrTail StrTail = True
sameFn StrIndex StrIndex = True
sameFn StrCons StrCons = True
sameFn StrAppend StrAppend = True
sameFn StrReverse StrReverse = True
sameFn StrSubstr StrSubstr = True
sameFn DoubleExp DoubleExp = True
sameFn DoubleLog DoubleLog = True
sameFn DoublePow DoublePow = True
sameFn DoubleSin DoubleSin = True
sameFn DoubleCos DoubleCos = True
sameFn DoubleTan DoubleTan = True
sameFn DoubleASin DoubleASin = True
sameFn DoubleACos DoubleACos = True
sameFn DoubleATan DoubleATan = True
sameFn DoubleSqrt DoubleSqrt = True
sameFn DoubleFloor DoubleFloor = True
sameFn DoubleCeiling DoubleCeiling = True
sameFn (Cast{}) (Cast{}) = True
sameFn BelieveMe BelieveMe = True
sameFn Crash Crash = True
sameFn _ _ = False

public export
data PiInfo t = Implicit | Explicit | AutoImplicit | DefImplicit t

namespace PiInfo
  export
  isImplicit : PiInfo t -> Bool
  isImplicit Explicit = False
  isImplicit _ = True

-- There's few places where we need the default - it's just when checking if
-- there's a default during elaboration - so often it's easier just to erase it
-- to a normal implicit
export
forgetDef : PiInfo t -> PiInfo t'
forgetDef Explicit = Explicit
forgetDef Implicit = Implicit
forgetDef AutoImplicit = AutoImplicit
forgetDef (DefImplicit t) = Implicit

export
Show t => Show (PiInfo t) where
  show Implicit = "Implicit"
  show Explicit = "Explicit"
  show AutoImplicit = "AutoImplicit"
  show (DefImplicit t) = "DefImplicit " ++ show t

export
eqPiInfoBy : (t -> u -> Bool) -> PiInfo t -> PiInfo u -> Bool
eqPiInfoBy eqT = go where

  go : PiInfo t -> PiInfo u -> Bool
  go Implicit Implicit = True
  go Explicit Explicit = True
  go AutoImplicit AutoImplicit = True
  go (DefImplicit t) (DefImplicit t') = eqT t t'
  go _ _ = False

export
Eq t => Eq (PiInfo t) where
  (==) = eqPiInfoBy (==)

-- Perhaps The 'RigCount' should be first class, and therefore 'type'?
-- We can revisit this later without too many drastic changes (as long as
-- we don't revisit it *too much* later)
public export
data Binder : Type -> Type where
     -- Lambda bound variables with their implicitness
     Lam : FC -> RigCount -> PiInfo type -> (ty : type) -> Binder type
     -- Let bound variables with their value
     Let : FC -> RigCount -> (val : type) -> (ty : type) -> Binder type
     -- Forall/pi bound variables with their implicitness
     Pi : FC -> RigCount -> PiInfo type -> (ty : type) -> Binder type
     -- pattern bound variables. The PiInfo gives the implicitness at the
     -- point it was bound (Explicit if it was explicitly named in the
     -- program)
     PVar : FC -> RigCount -> PiInfo type -> (ty : type) -> Binder type
     -- variable bound for an as pattern (Like a let, but no computational
     -- force, and only used on the lhs. Converted to a let on the rhs because
     -- we want the computational behaviour.)
     PLet : FC -> RigCount -> (val : type) -> (ty : type) -> Binder type
     -- the type of pattern bound variables
     PVTy : FC -> RigCount -> (ty : type) -> Binder type

%name Binder bd

public export
data WhyErased a
  = Placeholder
  | Impossible
  | Dotted a

export
Eq a => Eq (WhyErased a) where
  Placeholder == Placeholder = True
  Impossible == Impossible = False
  Dotted x == Dotted y = x == y
  _ == _ = False

%name WhyErased why

export
Functor WhyErased where
  map f = \case
    Placeholder => Placeholder
    Impossible => Impossible
    Dotted a => Dotted (f a)

export
Foldable WhyErased where
  foldr c n (Dotted a) = c a n
  foldr c n _ = n

export
Traversable WhyErased where
  traverse f = \case
    Placeholder => pure Placeholder
    Impossible => pure Impossible
    Dotted a => Dotted <$> f a

export
isLet : Binder t -> Bool
isLet (Let _ _ _ _) = True
isLet _ = False

export
binderLoc : Binder tm -> FC
binderLoc (Lam fc _ x ty) = fc
binderLoc (Let fc _ val ty) = fc
binderLoc (Pi fc _ x ty) = fc
binderLoc (PVar fc _ p ty) = fc
binderLoc (PLet fc _ val ty) = fc
binderLoc (PVTy fc _ ty) = fc

export
binderType : Binder tm -> tm
binderType (Lam _ _ x ty) = ty
binderType (Let _ _ val ty) = ty
binderType (Pi _ _ x ty) = ty
binderType (PVar _ _ _ ty) = ty
binderType (PLet _ _ val ty) = ty
binderType (PVTy _ _ ty) = ty

export
multiplicity : Binder tm -> RigCount
multiplicity (Lam _ c x ty) = c
multiplicity (Let _ c val ty) = c
multiplicity (Pi _ c x ty) = c
multiplicity (PVar _ c p ty) = c
multiplicity (PLet _ c val ty) = c
multiplicity (PVTy _ c ty) = c

export
piInfo : Binder tm -> PiInfo tm
piInfo (Lam _ c x ty) = x
piInfo (Let _ c val ty) = Explicit
piInfo (Pi _ c x ty) = x
piInfo (PVar _ c p ty) = p
piInfo (PLet _ c val ty) = Explicit
piInfo (PVTy _ c ty) = Explicit

export
isImplicit : Binder tm -> Bool
isImplicit = PiInfo.isImplicit . piInfo

export
setMultiplicity : Binder tm -> RigCount -> Binder tm
setMultiplicity (Lam fc _ x ty) c = Lam fc c x ty
setMultiplicity (Let fc _ val ty) c = Let fc c val ty
setMultiplicity (Pi fc _ x ty) c = Pi fc c x ty
setMultiplicity (PVar fc _ p ty) c = PVar fc c p ty
setMultiplicity (PLet fc _ val ty) c = PLet fc c val ty
setMultiplicity (PVTy fc _ ty) c = PVTy fc c ty

export
Functor PiInfo where
  map func Explicit = Explicit
  map func Implicit = Implicit
  map func AutoImplicit = AutoImplicit
  map func (DefImplicit t) = (DefImplicit (func t))

export
Foldable PiInfo where
  foldr f acc Implicit = acc
  foldr f acc Explicit = acc
  foldr f acc AutoImplicit = acc
  foldr f acc (DefImplicit x) = f x acc

export
Traversable PiInfo where
  traverse f Implicit = pure Implicit
  traverse f Explicit = pure Explicit
  traverse f AutoImplicit = pure AutoImplicit
  traverse f (DefImplicit x) = map DefImplicit (f x)

export
Functor Binder where
  map func (Lam fc c x ty) = Lam fc c (map func x) (func ty)
  map func (Let fc c val ty) = Let fc c (func val) (func ty)
  map func (Pi fc c x ty) = Pi fc c (map func x) (func ty)
  map func (PVar fc c p ty) = PVar fc c (map func p) (func ty)
  map func (PLet fc c val ty) = PLet fc c (func val) (func ty)
  map func (PVTy fc c ty) = PVTy fc c (func ty)

export
Foldable Binder where
  foldr f acc (Lam fc c x ty) = foldr f (f ty acc) x
  foldr f acc (Let fc c val ty) = f val (f ty acc)
  foldr f acc (Pi fc c x ty) = foldr f (f ty acc) x
  foldr f acc (PVar fc c p ty) = foldr f (f ty acc) p
  foldr f acc (PLet fc c val ty) = f val (f ty acc)
  foldr f acc (PVTy fc c ty) = f ty acc

export
Traversable Binder where
  traverse f (Lam fc c x ty) = Lam fc c <$> traverse f x <*> f ty
  traverse f (Let fc c val ty) = Let fc c <$> f val <*> f ty
  traverse f (Pi fc c x ty) = Pi fc c <$> traverse f x <*> f ty
  traverse f (PVar fc c p ty) = PVar fc c <$> traverse f p <*> f ty
  traverse f (PLet fc c val ty) = PLet fc c <$> f val <*> f ty
  traverse f (PVTy fc c ty) = PVTy fc c <$> f ty

public export
data IsVar : Name -> Nat -> SnocList Name -> Type where
     First : IsVar n Z (ns :< n)
     Later : IsVar n i ns -> IsVar n (S i) (ns :< m)

public export
data LazyReason = LInf | LLazy | LUnknown

-- For as patterns matching linear arguments, select which side is
-- consumed
public export
data UseSide = UseLeft | UseRight

public export
data CaseAlt : SnocList Name -> Type

-- A 'Case' arises either from a top level pattern match, or a 'case' block,
-- and it's useful to know the difference so we know when to stop reducing due
-- to a blocked top level function
public export
data CaseType = PatMatch | CaseBlock Name

export
Show CaseType where
  show PatMatch = "(pat)"
  show (CaseBlock n) = "(block " ++ show n ++ ")"

-- Typechecked terms
-- These are guaranteed to be well-scoped wrt local variables, because they are
-- indexed by the names of local variables in scope
public export
data Term : SnocList Name -> Type where
     Local : FC -> (idx : Nat) -> (0 p : IsVar name idx vars) -> Term vars
     Ref : FC -> NameType -> (name : Name) -> Term vars
     -- Metavariables and the scope they are applied to
     Meta : FC -> Name -> Int -> List (RigCount, Term vars) -> Term vars
     Bind : FC -> (x : Name) ->
            (b : Binder (Term vars)) ->
            (scope : Term (vars :< x)) -> Term vars
     App : FC -> (fn : Term vars) ->
           RigCount -> -- if fn : (q x : a) -> t, then this is 'q'
           (arg : Term vars) -> Term vars
     -- As patterns, including whether (in a linear setting) it's the name
     -- or the pattern that is consumed
     -- Since we check LHS patterns as terms before turning
     -- them into patterns, this helps us get it right. When normalising,
     -- we just reduce the inner term and ignore the 'as' part
     -- The 'as' part should really be a Name rather than a Term, but it's
     -- easier this way since it gives us the ability to work with unresolved
     -- names (Ref), metavariables (Meta) and resolved names (Local) without
     -- having to define a special purpose thing. (But it'd be nice to tidy
     -- that up, nevertheless)
     As : FC -> UseSide -> (as : Term vars) -> (pat : Term vars) -> Term vars
     Case : FC -> CaseType ->
            RigCount -> (sc : Term vars) -> (scTy : Term vars) ->
            List (CaseAlt vars) ->
            Term vars
     -- Typed laziness annotations
     TDelayed : FC -> LazyReason -> Term vars -> Term vars
     TDelay : FC -> LazyReason -> (ty : Term vars) -> (arg : Term vars) -> Term vars
     TForce : FC -> LazyReason -> Term vars -> Term vars
     PrimVal : FC -> (c : Constant) -> Term vars
     PrimOp : {arity : _} ->
              FC -> PrimFn arity -> Vect arity (Term vars) -> Term vars
     Erased : FC -> WhyErased (Term vars) -> Term vars
     Unmatched : FC -> String -> Term vars -- error from a partialmatch
     TType : FC -> Name -> -- universe variable
             Term vars

public export
ClosedTerm : Type
ClosedTerm = Term [<]

export
isErased : Term vars -> Bool
isErased (Erased _ _) = True
isErased _ = False

export
getLoc : Term vars -> FC
getLoc (Local fc _ _) = fc
getLoc (Ref fc _ _) = fc
getLoc (Meta fc _ _ _) = fc
getLoc (Bind fc _ _ _) = fc
getLoc (App fc _ _ _) = fc
getLoc (As fc _ _ _) = fc
getLoc (Case fc _ _ _ _ _) = fc
getLoc (TDelayed fc _ _) = fc
getLoc (TDelay fc _ _ _) = fc
getLoc (TForce fc _ _) = fc
getLoc (PrimVal fc _) = fc
getLoc (PrimOp fc _ _) = fc
getLoc (Erased fc _) = fc
getLoc (Unmatched fc _) = fc
getLoc (TType fc _) = fc

-- Constraints between names representing universe levels. Record the
-- origin of each name, for error message purposes
public export
data UConstraint : Type where
     ULT : FC -> Name -> FC -> Name -> UConstraint
     ULE : FC -> Name -> FC -> Name -> UConstraint

public export
data Var : SnocList Name -> Type where
     MkVar : {i : Nat} -> (0 p : IsVar n i vars) -> Var vars

-- Scope of a case expression - bind the arguments one by one, as this makes
-- more sense during evaluation and is consistent with the way we bind
-- arguments in 'Bind'.
public export
data CaseScope : SnocList Name -> Type where
     RHS : List (Var vars, Term vars) -> -- Forced equalities
           Term vars -> -- RHS
           CaseScope vars
     Arg : RigCount -> (x : Name) -> CaseScope (vars :< x) -> CaseScope vars

||| Case alternatives. Unlike arbitrary patterns, they can be at most
||| one constructor deep.
public export
data CaseAlt : SnocList Name -> Type where
     ||| Constructor for a data type; bind the arguments and subterms.
     ConCase : FC -> Name -> (tag : Int) -> CaseScope vars -> CaseAlt vars
     ||| Lazy match for the Delay type use for codata types
     DelayCase : FC -> (ty : Name) -> (arg : Name) ->
                 Term (vars :< ty :< arg) -> CaseAlt vars
     ||| Match against a literal
     ConstCase : FC -> Constant -> Term vars -> CaseAlt vars
     ||| Catch-all case
     DefaultCase : FC -> Term vars -> CaseAlt vars

export
isDefault : CaseAlt vars -> Bool
isDefault (DefaultCase _ _) = True
isDefault _ = False

public export
data Visibility = Private | Export | Public

export
Show Visibility where
  show Private = "private"
  show Export = "export"
  show Public = "public export"

export
Pretty Void Visibility where
  pretty Private = pretty0 "private"
  pretty Export = pretty0 "export"
  pretty Public = pretty0 "public" <+> pretty0 "export"

export
Eq Visibility where
  Private == Private = True
  Export == Export = True
  Public == Public = True
  _ == _ = False

export
Ord Visibility where
  compare Private Export = LT
  compare Private Public = LT
  compare Export Public = LT

  compare Private Private = EQ
  compare Export Export = EQ
  compare Public Public = EQ

  compare Export Private = GT
  compare Public Private = GT
  compare Public Export = GT

public export
data TotalReq = Total | CoveringOnly | PartialOK

export
Eq TotalReq where
    (==) Total Total = True
    (==) CoveringOnly CoveringOnly = True
    (==) PartialOK PartialOK = True
    (==) _ _ = False

||| Bigger means more requirements
||| So if a definition was checked at b, it can be accepted at a <= b.
export
Ord TotalReq where
  PartialOK <= _ = True
  _ <= Total = True
  a <= b = a == b

  a < b = a <= b && a /= b

export
Show TotalReq where
    show Total = "total"
    show CoveringOnly = "covering"
    show PartialOK = "partial"

public export
data PartialReason
       = NotStrictlyPositive
       | BadCall (List Name)
       -- sequence of mutually-recursive function calls leading to a non-terminating function
       | BadPath (List (FC, Name)) Name
       | RecPath (List (FC, Name))

export
Show PartialReason where
  show NotStrictlyPositive = "not strictly positive"
  show (BadCall [n])
      = "possibly not terminating due to call to " ++ show n
  show (BadCall ns)
      = "possibly not terminating due to calls to " ++ showSep ", " (map show ns)
  show (BadPath [_] n)
      = "possibly not terminating due to call  to " ++ show n
  show (BadPath init n)
      = "possibly not terminating due to function " ++ show n ++ " being reachable via " ++ showSep " -> " (map show init)
  show (RecPath loop)
      = "possibly not terminating due to recursive path " ++ showSep " -> " (map (show . snd) loop)

export
Pretty Void PartialReason where
  pretty NotStrictlyPositive = reflow "not strictly positive"
  pretty (BadCall [n])
    = reflow "possibly not terminating due to call to" <++> pretty n
  pretty (BadCall ns)
    = reflow "possibly not terminating due to calls to" <++> concatWith (surround (comma <+> space)) (pretty <$> ns)
  pretty (BadPath [_] n)
    = reflow "possibly not terminating due to call to" <++> pretty n
  pretty (BadPath init n)
    = reflow "possibly not terminating due to function" <++> pretty n
      <++> reflow "being reachable via"
      <++> concatWith (surround (pretty " -> ")) (pretty <$> map snd init)
  pretty (RecPath loop)
    = reflow "possibly not terminating due to recursive path" <++> concatWith (surround (pretty " -> ")) (pretty <$> map snd loop)

public export
data Terminating
       = Unchecked
       | IsTerminating
       | NotTerminating PartialReason

export
Show Terminating where
  show Unchecked = "not yet checked"
  show IsTerminating = "terminating"
  show (NotTerminating p) = show p

export
Pretty Void Terminating where
  pretty Unchecked = reflow "not yet checked"
  pretty IsTerminating = pretty0 "terminating"
  pretty (NotTerminating p) = pretty p

public export
data Covering
       = IsCovering
       | MissingCases (List (Term [<]))
       | NonCoveringCall (List Name)

export
Show Covering where
  show IsCovering = "covering"
  show (MissingCases c) = "not covering all cases"
  show (NonCoveringCall [f])
     = "not covering due to call to function " ++ show f
  show (NonCoveringCall cs)
     = "not covering due to calls to functions " ++ showSep ", " (map show cs)

export
Pretty Void Covering where
  pretty IsCovering = pretty0 "covering"
  pretty (MissingCases c) = reflow "not covering all cases"
  pretty (NonCoveringCall [f])
     = reflow "not covering due to call to function" <++> pretty f
  pretty (NonCoveringCall cs)
     = reflow "not covering due to calls to functions" <++> concatWith (surround (comma <+> space)) (pretty <$> cs)

-- Totality status of a definition. We separate termination checking from
-- coverage checking.
public export
record Totality where
     constructor MkTotality
     isTerminating : Terminating
     isCovering : Covering

export
Show Totality where
  show tot
    = let t = isTerminating tot
          c = isCovering tot in
        showTot t c
    where
      showTot : Terminating -> Covering -> String
      showTot IsTerminating IsCovering = "total"
      showTot IsTerminating c = show c
      showTot t IsCovering = show t
      showTot t c = show c ++ "; " ++ show t

export
Pretty Void Totality where
  pretty (MkTotality IsTerminating IsCovering) = pretty0 "total"
  pretty (MkTotality IsTerminating c) = pretty c
  pretty (MkTotality t IsCovering) = pretty t
  pretty (MkTotality t c) = pretty c <+> semi <++> pretty t

export
unchecked : Totality
unchecked = MkTotality Unchecked IsCovering

export
isTotal : Totality
isTotal = MkTotality Unchecked IsCovering

export
notCovering : Totality
notCovering = MkTotality Unchecked (MissingCases [])

public export
record KindedName where
  constructor MkKindedName
  nameKind : Maybe NameType
  fullName : Name -- fully qualified name
  rawName  : Name

export
defaultKindedName : Name -> KindedName
defaultKindedName nm = MkKindedName Nothing nm nm

export
funKindedName : Name -> KindedName
funKindedName nm = MkKindedName (Just Func) nm nm

export
Show KindedName where show = show . rawName

export
covering
[Raw] Show KindedName where
  showPrec d (MkKindedName nm fn rn) =
    showCon d "MkKindedName" $ showArg nm ++ showArg @{Raw} fn ++ showArg @{Raw} rn

public export
data DotReason = NonLinearVar
               | VarApplied
               | NotConstructor
               | ErasedArg
               | UserDotted
               | UnknownDot
               | UnderAppliedCon

export
Show DotReason where
  show NonLinearVar = "Non linear pattern variable"
  show VarApplied = "Variable applied to arguments"
  show NotConstructor = "Not a constructor application or primitive"
  show ErasedArg = "Erased argument"
  show UserDotted = "User dotted"
  show UnknownDot = "Unknown reason"
  show UnderAppliedCon = "Under-applied constructor"

export
Pretty ann DotReason where
  pretty NonLinearVar = reflow "Non linear pattern variable"
  pretty VarApplied = reflow "Variable applied to arguments"
  pretty NotConstructor = reflow "Not a constructor application or primitive"
  pretty ErasedArg = reflow "Erased argument"
  pretty UserDotted = reflow "User dotted"
  pretty UnknownDot = reflow "Unknown reason"
  pretty UnderAppliedCon = reflow "Under-applied constructor"

export
Eq LazyReason where
  (==) LInf LInf = True
  (==) LLazy LLazy = True
  (==) LUnknown LUnknown = True
  (==) _ _ = False

export
Show LazyReason where
    show LInf = "Inf"
    show LLazy = "Lazy"
    show LUnknown = "Unkown"

export
compatible : LazyReason -> LazyReason -> Bool
compatible LUnknown _ = True
compatible _ LUnknown = True
compatible x y = x == y

export
eqBinderBy : (t -> u -> Bool) -> (Binder t -> Binder u -> Bool)
eqBinderBy eqTU = go where

  go : Binder t -> Binder u -> Bool
  go (Lam _ c p ty) (Lam _ c' p' ty') = c == c' && eqPiInfoBy eqTU p p' && eqTU ty ty'
  go (Let _ c v ty) (Let _ c' v' ty') = c == c' && eqTU v v' && eqTU ty ty'
  go (Pi _ c p ty) (Pi _ c' p' ty')   = c == c' && eqPiInfoBy eqTU p p' && eqTU ty ty'
  go (PVar _ c p ty) (PVar _ c' p' ty') = c == c' && eqPiInfoBy eqTU p p' && eqTU ty ty'
  go (PLet _ c v ty) (PLet _ c' v' ty') = c == c' && eqTU v v' && eqTU ty ty'
  go (PVTy _ c ty) (PVTy _ c' ty') = c == c' && eqTU ty ty'
  go _ _ = False
