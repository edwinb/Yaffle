module Core.TT.TT

import public Core.FC
import public Core.TT.Name
import public Core.TT.RigCount

import Data.Vect
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
    | WorldVal

    | IntType
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

export
isConstantType : Name -> Maybe Constant
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
  show WorldVal = "%MkWorld"
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
Pretty ann Constant where
  pretty (Str x) = dquotes (pretty0 x)
  pretty (Ch x) = squotes (pretty0 x)
  pretty x = pretty0 $ show x

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
  WorldVal == WorldVal = True
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

-- for typecase
export
constTag : Constant -> Int
-- 1 = ->, 2 = Type
constTag IntType = 3
constTag IntegerType = 4
constTag Bits8Type = 5
constTag Bits16Type = 6
constTag Bits32Type = 7
constTag Bits64Type = 8
constTag StringType = 9
constTag CharType = 10
constTag DoubleType = 11
constTag WorldType = 12
constTag Int8Type = 13
constTag Int16Type = 14
constTag Int32Type = 15
constTag Int64Type = 16
constTag _ = 0

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
intKind : Constant -> Maybe IntKind
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
     Add : (ty : Constant) -> PrimFn 2
     Sub : (ty : Constant) -> PrimFn 2
     Mul : (ty : Constant) -> PrimFn 2
     Div : (ty : Constant) -> PrimFn 2
     Mod : (ty : Constant) -> PrimFn 2
     Neg : (ty : Constant) -> PrimFn 1
     ShiftL : (ty : Constant) -> PrimFn 2
     ShiftR : (ty : Constant) -> PrimFn 2

     BAnd : (ty : Constant) -> PrimFn 2
     BOr : (ty : Constant) -> PrimFn 2
     BXOr : (ty : Constant) -> PrimFn 2

     LT  : (ty : Constant) -> PrimFn 2
     LTE : (ty : Constant) -> PrimFn 2
     EQ  : (ty : Constant) -> PrimFn 2
     GTE : (ty : Constant) -> PrimFn 2
     GT  : (ty : Constant) -> PrimFn 2

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

     Cast : Constant -> Constant -> PrimFn 1
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
data AsName : SnocList Name -> Type where
     -- resolved name
     AsLoc : FC -> (idx : Nat) -> (0 p : IsVar name idx vars) -> AsName vars
     -- not yet resolved name
     AsRef : FC -> Name -> AsName vars

public export
data CaseAlt : SnocList Name -> Type

public export
data PatternClause : SnocList Name -> Type

-- Typechecked terms
-- These are guaranteed to be well-scoped wrt local variables, because they are
-- indexed by the names of local variables in scope
public export
data Term : SnocList Name -> Type where
     Local : FC -> Maybe Bool -> -- Is it a let bound local?
             (idx : Nat) -> (0 p : IsVar name idx vars) -> Term vars
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
     As : FC -> UseSide -> (as : AsName vars) -> (pat : Term vars) -> Term vars
     Case : FC -> (sc : Term vars) -> (scTy : Term vars) ->
            List (CaseAlt vars) ->
            Term vars
     -- Typed laziness annotations
     TDelayed : FC -> LazyReason -> Term vars -> Term vars
     TDelay : FC -> LazyReason -> (ty : Term vars) -> (arg : Term vars) -> Term vars
     TForce : FC -> LazyReason -> Term vars -> Term vars
     PrimVal : FC -> (c : Constant) -> Term vars
     PrimOp : FC -> PrimFn arity -> Vect arity (Term vars) -> Term vars
     Erased : FC -> (imp : Bool) -> -- True == impossible term, for coverage checker
              Term vars
     Unmatched : FC -> String -> Term vars -- error from a partialmatch
     Impossible : FC -> Term vars --impossible case
     TType : FC -> Name -> -- universe variable
             Term vars

-- Constraints between names representing universe levels. Record the
-- origin of each name, for error message purposes
public export
data UConstraint : Type where
     ULT : FC -> Name -> FC -> Name -> UConstraint
     ULE : FC -> Name -> FC -> Name -> UConstraint

-- Scope of a case expression - bind the arguments one by one, as this makes
-- more sense during evaluation and is consistent with the way we bind
-- arguments in 'Bind'.
public export
data CaseScope : SnocList Name -> Type where
     RHS : Term vars -> CaseScope vars
     Arg : (x : Name) -> CaseScope (vars :< x) -> CaseScope vars

||| Case alternatives. Unlike arbitrary patterns, they can be at most
||| one constructor deep.
public export
data CaseAlt : SnocList Name -> Type where
     ||| Constructor for a data type; bind the arguments and subterms.
     ConCase : Name -> (tag : Int) -> CaseScope vars -> CaseAlt vars
     ||| Lazy match for the Delay type use for codata types
     DelayCase : (ty : Name) -> (arg : Name) ->
                 Term (vars :< arg :< ty) -> CaseAlt vars
     ||| Match against a literal
     ConstCase : Constant -> Term vars -> CaseAlt vars
     ||| Catch-all case
     DefaultCase : Term vars -> CaseAlt vars

public export
data Visibility = Private | Export | Public

export
Show Visibility where
  show Private = "private"
  show Export = "export"
  show Public = "public export"

export
Pretty ann Visibility where
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
       | RecPath (List Name)

export
Show PartialReason where
  show NotStrictlyPositive = "not strictly positive"
  show (BadCall [n])
      = "possibly not terminating due to call to " ++ show n
  show (BadCall ns)
      = "possibly not terminating due to calls to " ++ showSep ", " (map show ns)
  show (RecPath ns)
      = "possibly not terminating due to recursive path " ++ showSep " -> " (map show ns)

export
Pretty ann PartialReason where
  pretty NotStrictlyPositive = reflow "not strictly positive"
  pretty (BadCall [n])
    = reflow "possibly not terminating due to call to" <++> pretty n
  pretty (BadCall ns)
    = reflow "possibly not terminating due to calls to" <++> concatWith (surround (comma <+> space)) (pretty <$> ns)
  pretty (RecPath ns)
    = reflow "possibly not terminating due to recursive path" <++> concatWith (surround (pretty0 " -> ")) (pretty <$> ns)

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
Pretty ann Terminating where
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
Pretty ann Covering where
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
Pretty ann Totality where
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
Show KindedName where show = show . rawName

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
