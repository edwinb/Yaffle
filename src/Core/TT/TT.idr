module Core.TT.TT

import public Core.FC
import public Core.TT.Name
import public Core.TT.RigCount

public export
Tag : Type
Tag = Integer

public export
data NameType : Type where
     Bound   : NameType
     Func    : NameType
     DataCon : (tag : Tag) -> (arity : Nat) -> NameType
     TyCon   : (tag : Tag) -> (arity : Nat) -> NameType

public export
data Constant =
       I Integer
     | Str String
     | Ch Char
     | Db Double
     | WorldVal

     | IntegerType
     | StringType
     | CharType
     | DoubleType
     | WorldType

export
Show Constant where
  show (I x) = show x
  show (Str x) = show x
  show (Ch x) = show x
  show (Db x) = show x
  show WorldVal = "%MkWorld"

  show IntegerType = "Integer"
  show StringType = "String"
  show CharType = "Char"
  show DoubleType = "Double"
  show WorldType = "%World"

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

public export
data IsVar : Name -> Nat -> List Name -> Type where
     First : IsVar n Z (n :: ns)
     Later : IsVar n i ns -> IsVar n (S i) (m :: ns)

public export
data LazyReason = LInf | LLazy | LUnknown

-- For as patterns matching linear arguments, select which side is
-- consumed
public export
data UseSide = UseLeft | UseRight

public export
data AsName : List Name -> Type where
     -- resolved name
     AsLoc : FC -> (idx : Nat) -> (0 p : IsVar name idx vars) -> AsName vars
     -- not yet resolved name
     AsRef : FC -> Name -> AsName vars

-- Terms use case-trees, case-trees refer to terms, so forward declare
public export
data CaseTree : List Name -> Type

public export
data CaseAlt : List Name -> Type

public export
data PatternClause : List Name -> Type

-- Typechecked terms
-- These are guaranteed to be well-scoped wrt local variables, because they are
-- indexed by the names of local variables in scope
public export
data Term : List Name -> Type where
     Local : FC -> (isLet : Maybe Bool) ->
             (idx : Nat) -> (0 p : IsVar name idx vars) -> Term vars
     Ref : FC -> NameType -> (name : Name) -> Term vars
     -- Metavariables and the scope they are applied to
     Meta : FC -> Name -> Int -> List (Term vars) -> Term vars
     Bind : FC -> (x : Name) ->
            (b : Binder (Term vars)) ->
            (scope : Term (x :: vars)) -> Term vars
     App : FC -> (fn : Term vars) -> (arg : Term vars) -> Term vars
     -- As patterns, including whether (in a linear setting) it's the name
     -- or the pattern that is consumed
     As : FC -> UseSide -> (as : AsName vars) -> (pat : Term vars) -> Term vars

     -- Case expressions, including initial patterns (optionally) and the
     -- compiled case trees
     Case : FC ->
            Maybe (List (PatternClause vars)) ->
            CaseTree vars -> Term vars

     -- Typed laziness annotations
     TDelayed : FC -> LazyReason -> Term vars -> Term vars
     TDelay : FC -> LazyReason -> (ty : Term vars) -> (arg : Term vars) -> Term vars
     TForce : FC -> LazyReason -> Term vars -> Term vars
     PrimVal : FC -> (c : Constant) -> Term vars
     Erased : FC -> (imp : Bool) -> -- True == impossible term, for coverage checker
              Term vars
     TType : FC -> Name -> -- universe variable
             Term vars

||| Pattern matching clause, before compilation to case trees
public export
data PatternClause : List Name -> Type where

||| Case trees in A-normal forms
||| i.e. we may only dispatch on variables, not expressions
public export
data CaseTree : List Name -> Type where
     ||| case x return scTy of { p1 => e1 ; ... }
     Switch : {name : _} ->
              (idx : Nat) ->
              (0 p : IsVar name idx vars) ->
              (scTy : Term vars) -> List (CaseAlt vars) ->
              CaseTree vars
     ||| RHS: no need for further inspection
     ||| The Int is a clause id that allows us to see which of the
     ||| initial clauses are reached in the tree
     STerm : Int -> Term vars -> CaseTree vars
     ||| error from a partial match
     Unmatched : (msg : String) -> CaseTree vars
     ||| Absurd context
     Impossible : CaseTree vars

||| Case alternatives. Unlike arbitrary patterns, they can be at most
||| one constructor deep.
public export
data CaseAlt : List Name -> Type where
     ||| Constructor for a data type; bind the arguments and subterms.
     ConCase : Name -> (tag : Int) -> (args : List Name) ->
               CaseTree (args ++ vars) -> CaseAlt vars
     ||| Lazy match for the Delay type use for codata types
     DelayCase : (ty : Name) -> (arg : Name) ->
                 CaseTree (ty :: arg :: vars) -> CaseAlt vars
     ||| Match against a literal
     ConstCase : Constant -> CaseTree vars -> CaseAlt vars
     ||| Catch-all case
     DefaultCase : CaseTree vars -> CaseAlt vars
