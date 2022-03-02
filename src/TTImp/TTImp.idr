module TTImp.TTImp

import Core.Context
import Core.Error
import Core.Options
import Core.TT

-- Unchecked terms, with implicit arguments
-- This is the raw, elaboratable form.
-- Higher level expressions (e.g. case, pattern matching let, where blocks,
-- do notation, etc, should elaborate via this, perhaps in some local
-- context).
public export
data BindMode = PI RigCount | PATTERN | COVERAGE | NONE

-- Forward declare everything here
public export
RawImp : Type

public export
IRawImp : Type

public export
ImpClause : Type

public export
IImpClause : Type

public export
data ImpClause' : Type -> Type

public export
IFieldUpdate : Type

public export
data IFieldUpdate' : Type -> Type

public export
AltType : Type

public export
data AltType' : Type -> Type where

public export
data RawImp' : Type -> Type where

public export
FnOpt : Type

public export
data FnOpt' : Type -> Type

public export
isTotalityReq : FnOpt' nm -> Bool

public export
ImpTy : Type

public export
data ImpTy' : Type -> Type

public export
data DataOpt : Type

public export
ImpData : Type

public export
data ImpData' : Type -> Type

-- TODO: turn into a proper datatype when possible.
-- Annoyingly records don't forward declare
public export
ImpParameter' : Type -> Type

public export
ImpDecl : Type

public export
data ImpDecl' : Type -> Type

public export
IField : Type

public export
data IField' : Type -> Type

public export
ImpRecord : Type

public export
data ImpRecord' : Type -> Type

--- Definitions here

RawImp = RawImp' Name
IRawImp = RawImp' KindedName
ImpClause = ImpClause' Name
IImpClause = ImpClause' KindedName
IFieldUpdate = IFieldUpdate' Name
AltType = AltType' Name
FnOpt = FnOpt' Name
ImpTy = ImpTy' Name
ImpData = ImpData' Name
ImpParameter' nm = (Name, RigCount, PiInfo (RawImp' nm), RawImp' nm)
ImpDecl = ImpDecl' Name
IField = IField' Name
ImpRecord = ImpRecord' Name


public export
data FnOpt' : Type -> Type where
     Inline : FnOpt' nm
     NoInline : FnOpt' nm
     ||| Mark a function as deprecated.
     Deprecate : FnOpt' nm
     TCInline : FnOpt' nm
     -- Flag means the hint is a direct hint, not a function which might
     -- find the result (e.g. chasing parent interface dictionaries)
     Hint : Bool -> FnOpt' nm
     -- Flag means to use as a default if all else fails
     GlobalHint : Bool -> FnOpt' nm
     ExternFn : FnOpt' nm
     -- Defined externally, list calling conventions
     ForeignFn : List (RawImp' nm) -> FnOpt' nm
     -- assume safe to cancel arguments in unification
     Invertible : FnOpt' nm
     Totality : TotalReq -> FnOpt' nm
     Macro : FnOpt' nm
     SpecArgs : List Name -> FnOpt' nm
     NoMangle : Maybe NoMangleDirective -> FnOpt' nm

isTotalityReq (Totality _) = True
isTotalityReq _ = False

public export
data WithFlag
       = Syntactic -- abstract syntactically, rather than by value

public export
data ImpClause' : Type -> Type where
     PatClause : FC -> (lhs : RawImp' nm) -> (rhs : RawImp' nm) -> ImpClause' nm
     WithClause : FC -> (lhs : RawImp' nm) ->
                  (wval : RawImp' nm) -> (prf : Maybe Name) ->
                  (flags : List WithFlag) ->
                  List (ImpClause' nm) -> ImpClause' nm
     ImpossibleClause : FC -> (lhs : RawImp' nm) -> ImpClause' nm

public export
data IFieldUpdate' : Type -> Type where
     ISetField : (path : List String) -> RawImp' nm -> IFieldUpdate' nm
     ISetFieldApp : (path : List String) -> RawImp' nm -> IFieldUpdate' nm

public export
data AltType' : Type -> Type where
     FirstSuccess : AltType' nm
     Unique : AltType' nm
     UniqueDefault : RawImp' nm -> AltType' nm

public export
data RawImp' : Type -> Type where
     IVar : FC -> nm -> RawImp' nm
     IPi : FC -> RigCount -> PiInfo (RawImp' nm) -> Maybe Name ->
           (argTy : RawImp' nm) -> (retTy : RawImp' nm) -> RawImp' nm
     ILam : FC -> RigCount -> PiInfo (RawImp' nm) -> Maybe Name ->
            (argTy : RawImp' nm) -> (lamTy : RawImp' nm) -> RawImp' nm
     ILet : FC -> (lhsFC : FC) -> RigCount -> Name ->
            (nTy : RawImp' nm) -> (nVal : RawImp' nm) ->
            (scope : RawImp' nm) -> RawImp' nm
     ICase : FC -> RawImp' nm -> (ty : RawImp' nm) ->
             List (ImpClause' nm) -> RawImp' nm

     IUpdate : FC -> List (IFieldUpdate' nm) -> RawImp' nm -> RawImp' nm

     IApp : FC -> RawImp' nm -> RawImp' nm -> RawImp' nm
     IAutoApp : FC -> RawImp' nm -> RawImp' nm -> RawImp' nm
     INamedApp : FC -> RawImp' nm -> Name -> RawImp' nm -> RawImp' nm
     IWithApp : FC -> RawImp' nm -> RawImp' nm -> RawImp' nm

     ISearch : FC -> (depth : Nat) -> RawImp' nm
     IAlternative : FC -> AltType' nm -> List (RawImp' nm) -> RawImp' nm
     IRewrite : FC -> RawImp' nm -> RawImp' nm -> RawImp' nm
     ICoerced : FC -> RawImp' nm -> RawImp' nm

     -- Any implicit bindings in the scope should be bound here, using
     -- the given binder
     IBindHere : FC -> BindMode -> RawImp' nm -> RawImp' nm
     -- A name which should be implicitly bound
     IBindVar : FC -> String -> RawImp' nm
     -- An 'as' pattern, valid on the LHS of a clause only
     IAs : FC -> (nameFC : FC) -> UseSide -> Name -> RawImp' nm -> RawImp' nm
     -- A 'dot' pattern, i.e. one which must also have the given value
     -- by unification
     IMustUnify : FC -> DotReason -> RawImp' nm -> RawImp' nm

     -- Laziness annotations
     IDelayed : FC -> LazyReason -> RawImp' nm -> RawImp' nm -- the type
     IDelay : FC -> RawImp' nm -> RawImp' nm -- delay constructor
     IForce : FC -> RawImp' nm -> RawImp' nm

     -- Quasiquoting
     IQuote : FC -> RawImp' nm -> RawImp' nm
     IQuoteName : FC -> Name -> RawImp' nm
     IQuoteDecl : FC -> List (ImpDecl' nm) -> RawImp' nm
     IUnquote : FC -> RawImp' nm -> RawImp' nm
     IRunElab : FC -> RawImp' nm -> RawImp' nm

     IPrimVal : FC -> (c : Constant) -> RawImp' nm
     IType : FC -> RawImp' nm
     IHole : FC -> String -> RawImp' nm

     IUnifyLog : FC -> LogLevel -> RawImp' nm -> RawImp' nm
     -- An implicit value, solved by unification, but which will also be
     -- bound (either as a pattern variable or a type variable) if unsolved
     -- at the end of elaborator
     Implicit : FC -> (bindIfUnsolved : Bool) -> RawImp' nm

     -- with-disambiguation
     IWithUnambigNames : FC -> List Name -> RawImp' nm -> RawImp' nm

public export
data ImpTy' : Type -> Type where
     MkImpTy : FC -> (nameFC : FC) -> (n : Name) -> (ty : RawImp' nm) -> ImpTy' nm

public export
data DataOpt : Type where
     SearchBy : List Name -> DataOpt -- determining arguments
     NoHints : DataOpt -- Don't generate search hints for constructors
     UniqueSearch : DataOpt -- auto implicit search must check result is unique
     External : DataOpt -- implemented externally
     NoNewtype : DataOpt -- don't apply newtype optimisation

public export
data ImpData' : Type -> Type where
     MkImpData : FC -> (n : Name) -> (tycon : RawImp' nm) ->
                 (opts : List DataOpt) ->
                 (datacons : List (ImpTy' nm)) -> ImpData' nm
     MkImpLater : FC -> (n : Name) -> (tycon : RawImp' nm) -> ImpData' nm

public export
data ImpDecl' : Type -> Type where
     IClaim : FC -> RigCount -> Visibility -> List (FnOpt' nm) ->
              ImpTy' nm -> ImpDecl' nm
     IData : FC -> Visibility -> Maybe TotalReq -> ImpData' nm -> ImpDecl' nm
     IDef : FC -> Name -> RawImp' nm -> ImpDecl' nm
     IParameters : FC ->
                   List (ImpParameter' nm) ->
                   List (ImpDecl' nm) -> ImpDecl' nm
     IRecord : FC ->
               Maybe String -> -- nested namespace
               Visibility -> Maybe TotalReq ->
               ImpRecord' nm -> ImpDecl' nm
     INamespace : FC -> Namespace -> List (ImpDecl' nm) -> ImpDecl' nm
     ITransform : FC -> Name -> RawImp' nm -> RawImp' nm -> ImpDecl' nm
     IRunElabDecl : FC -> RawImp' nm -> ImpDecl' nm
     -- TODO: Put it back when we've worked out what an Env is!
--      IPragma : List Name -> -- pragmas might define names that wouldn't
--                      -- otherwise be spotted in 'definedInBlock' so they
--                      -- can be flagged here.
--                ({vars : _} -> Env Term vars -> Core ()) ->
--                ImpDecl' nm
     ILog : Maybe (List String, Nat) -> ImpDecl' nm
     IBuiltin : FC -> BuiltinType -> Name -> ImpDecl' nm

public export
data IField' : Type -> Type where
     MkIField : FC -> RigCount -> PiInfo (RawImp' nm) -> Name -> RawImp' nm ->
                IField' nm

public export
data ImpRecord' : Type -> Type where
     MkImpRecord : FC -> (n : Name) ->
                   (params : List (ImpParameter' nm)) ->
                   (conName : Name) ->
                   (fields : List (IField' nm)) ->
                   ImpRecord' nm

-- Implementations

export
Eq WithFlag where
    Syntactic == Syntactic = True

export
Eq DataOpt where
  (==) (SearchBy xs) (SearchBy ys) = xs == ys
  (==) NoHints NoHints = True
  (==) UniqueSearch UniqueSearch = True
  (==) External External = True
  (==) NoNewtype NoNewtype = True
  (==) _ _ = False

-- TODO: Fix this, we need to be able to forward declare implementations
mutual
  export
  covering
  Show nm => Show (RawImp' nm) where
      show (IVar fc n) = show n
      show (IPi fc c p n arg ret)
         = "(%pi " ++ show c ++ " " ++ show p ++ " " ++
           showPrec App n ++ " " ++ show arg ++ " " ++ show ret ++ ")"
      show (ILam fc c p n arg sc)
         = "(%lam " ++ show c ++ " " ++ show p ++ " " ++
           showPrec App n ++ " " ++ show arg ++ " " ++ show sc ++ ")"
      show (ILet fc lhsFC c n ty val sc)
         = "(%let " ++ show c ++ " " ++ " " ++ show n ++ " " ++ show ty ++
           " " ++ show val ++ " " ++ show sc ++ ")"
      show (ICase _ scr scrty alts)
         = "(%case (" ++ show scr ++ " : " ++ show scrty ++ ") " ++ show alts ++ ")"
      show (IUpdate _ flds rec)
         = "(%record " ++ showSep ", " (map show flds) ++ " " ++ show rec ++ ")"
      show (IApp fc f a)
         = "(" ++ show f ++ " " ++ show a ++ ")"
      show (INamedApp fc f n a)
         = "(" ++ show f ++ " [" ++ show n ++ " = " ++ show a ++ "])"
      show (IAutoApp fc f a)
         = "(" ++ show f ++ " [" ++ show a ++ "])"
      show (IWithApp fc f a)
         = "(" ++ show f ++ " | " ++ show a ++ ")"
      show (ISearch fc d)
         = "%search"
      show (IAlternative fc ty alts)
         = "(|" ++ showSep "," (map show alts) ++ "|)"
      show (IRewrite _ rule tm)
         = "(%rewrite (" ++ show rule ++ ") (" ++ show tm ++ "))"
      show (ICoerced _ tm) = "(%coerced " ++ show tm ++ ")"

      show (IBindHere fc b sc)
         = "(%bindhere " ++ show sc ++ ")"
      show (IBindVar fc n) = "$" ++ n
      show (IAs fc _ _ n tm) = show n ++ "@(" ++ show tm ++ ")"
      show (IMustUnify fc r tm) = ".(" ++ show tm ++ ")"
      show (IDelayed fc r tm) = "(%delayed " ++ show tm ++ ")"
      show (IDelay fc tm) = "(%delay " ++ show tm ++ ")"
      show (IForce fc tm) = "(%force " ++ show tm ++ ")"
      show (IQuote fc tm) = "(%quote " ++ show tm ++ ")"
      show (IQuoteName fc tm) = "(%quotename " ++ show tm ++ ")"
      show (IQuoteDecl fc tm) = "(%quotedecl " ++ show tm ++ ")"
      show (IUnquote fc tm) = "(%unquote " ++ show tm ++ ")"
      show (IRunElab fc tm) = "(%runelab " ++ show tm ++ ")"
      show (IPrimVal fc c) = show c
      show (IHole _ x) = "?" ++ x
      show (IUnifyLog _ lvl x) = "(%logging " ++ show lvl ++ " " ++ show x ++ ")"
      show (IType fc) = "%type"
      show (Implicit fc True) = "_"
      show (Implicit fc False) = "?"
      show (IWithUnambigNames fc ns rhs) = "(%with " ++ show ns ++ " " ++ show rhs ++ ")"

  export
  covering
  Show nm => Show (IFieldUpdate' nm) where
    show (ISetField p val) = showSep "->" p ++ " = " ++ show val
    show (ISetFieldApp p val) = showSep "->" p ++ " $= " ++ show val

  export
  Show NoMangleDirective where
    show (CommonName name) = "\"\{name}\""
    show (BackendNames ns) = showSep " " (map (\(b, n) => "\"\{b}:\{n}\"") ns)

  export
  covering
  Show nm => Show (FnOpt' nm) where
    show Inline = "%inline"
    show NoInline = "%noinline"
    show Deprecate = "%deprecate"
    show TCInline = "%tcinline"
    show (Hint t) = "%hint " ++ show t
    show (GlobalHint t) = "%globalhint " ++ show t
    show ExternFn = "%extern"
    show (ForeignFn cs) = "%foreign " ++ showSep " " (map show cs)
    show Invertible = "%invertible"
    show (Totality Total) = "total"
    show (Totality CoveringOnly) = "covering"
    show (Totality PartialOK) = "partial"
    show Macro = "%macro"
    show (SpecArgs ns) = "%spec " ++ showSep " " (map show ns)
    show (NoMangle Nothing) = "%nomangle"
    show (NoMangle (Just ns)) = "%nomangle \{show ns}"

  export
  Eq NoMangleDirective where
    CommonName x == CommonName y = x == y
    BackendNames xs == BackendNames ys = xs == ys
    _ == _ = False

  export
  Eq FnOpt where
    Inline == Inline = True
    NoInline == NoInline = True
    Deprecate == Deprecate = True
    TCInline == TCInline = True
    (Hint x) == (Hint y) = x == y
    (GlobalHint x) == (GlobalHint y) = x == y
    ExternFn == ExternFn = True
    (ForeignFn xs) == (ForeignFn ys) = True -- xs == ys
    Invertible == Invertible = True
    (Totality tot_lhs) == (Totality tot_rhs) = tot_lhs == tot_rhs
    Macro == Macro = True
    (SpecArgs ns) == (SpecArgs ns') = ns == ns'
    (NoMangle x) == (NoMangle y) = x == y
    _ == _ = False

  export
  covering
  Show nm => Show (ImpTy' nm) where
    show (MkImpTy fc _ n ty) = "(%claim " ++ show n ++ " " ++ show ty ++ ")"

  export
  covering
  Show nm => Show (ImpData' nm) where
    show (MkImpData fc n tycon _ cons)
        = "(%data " ++ show n ++ " " ++ show tycon ++ " " ++
           show cons ++ ")"
    show (MkImpLater fc n tycon)
        = "(%datadecl " ++ show n ++ " " ++ show tycon ++ ")"

  export
  covering
  Show nm => Show (IField' nm) where
    show (MkIField _ c Explicit n ty) = show n ++ " : " ++ show ty
    show (MkIField _ c _ n ty) = "{" ++ show n ++ " : " ++ show ty ++ "}"

  export
  covering
  Show nm => Show (ImpRecord' nm) where
    show (MkImpRecord _ n params con fields)
        = "record " ++ show n ++ " " ++ show params ++
          " " ++ show con ++ "\n\t" ++
          showSep "\n\t" (map show fields) ++ "\n"

  export
  covering
  Show nm => Show (ImpClause' nm) where
    show (PatClause fc lhs rhs)
       = show lhs ++ " = " ++ show rhs
    show (WithClause fc lhs wval prf flags block)
       = show lhs
       ++ " with " ++ show wval
       ++ maybe "" (\ nm => " proof " ++ show nm) prf
       ++ "\n\t" ++ show block
    show (ImpossibleClause fc lhs)
       = show lhs ++ " impossible"

  export
  covering
  Show nm => Show (ImpDecl' nm) where
    show (IClaim _ c _ opts ty) = show opts ++ " " ++ show c ++ " " ++ show ty
    show (IData _ _ _ d) = show d
    show (IDef _ n cs) = "(%def " ++ show n ++ " " ++ show cs ++ ")"
    show (IParameters _ ps ds)
        = "parameters " ++ show ps ++ "\n\t" ++
          showSep "\n\t" (assert_total $ map show ds)
    show (IRecord _ _ _ _ d) = show d
    show (INamespace _ ns decls)
        = "namespace " ++ show ns ++
          showSep "\n" (assert_total $ map show decls)
    show (ITransform _ n lhs rhs)
        = "%transform " ++ show n ++ " " ++ show lhs ++ " ==> " ++ show rhs
    show (IRunElabDecl _ tm)
        = "%runElab " ++ show tm
  --   show (IPragma _ _) = "[externally defined pragma]"
    show (ILog Nothing) = "%logging off"
    show (ILog (Just (topic, lvl))) = "%logging " ++ case topic of
      [] => show lvl
      _  => concat (intersperse "." topic) ++ " " ++ show lvl
    show (IBuiltin _ type name) = "%builtin " ++ show type ++ " " ++ show name
