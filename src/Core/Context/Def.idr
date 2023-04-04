module Core.Context.Def

-- This module includes:
-- * The forms of definition (function, data type etc)

import Core.TT
import Core.Env

import Data.SnocList

public export
data HoleInfo
        = NotHole
        | SolvedHole Nat

public export
record FnInfo where
  constructor MkFnInfo
  holeInfo : HoleInfo -- data if it comes from a solved hole
  alwaysReduce : Bool -- always reduce - typically for inlinable metavariable solutions
  externalDecl : Bool -- declared in another module, which may affect how it
                      -- is compiled

export
defaultFI : FnInfo
defaultFI = MkFnInfo NotHole False False

export
reduceFI : FnInfo
reduceFI = MkFnInfo NotHole True False

public export
record DataConInfo where
  constructor MkDataConInfo
  quantities : List RigCount
               -- Quantities on arguments
  newTypeArg : Maybe (Bool, Nat)
               -- if it's the only constructor, and only one argument is
               -- non-Rig0, flag it here.
               -- The Nat is the unerased argument position.
               -- The Bool is 'True' if there is no %World token in the
               -- structure, which means it is safe to completely erase
               -- when pattern matching (otherwise we still have to ensure
               -- that the value is inspected, to make sure external effects
               -- happen)

export
defaultDataConInfo : List RigCount -> DataConInfo
defaultDataConInfo qs = MkDataConInfo qs Nothing

public export
record TyConInfo where
  constructor MkTyConInfo
  paramPos : List Nat -- parameter positions
  deterArgs : List Nat -- determining argument positions (for search)
  mutWith : List Name -- Names this type is defined with mutually
  datacons : List Name -- This type's data constructors
  detagBy : Maybe (List Nat)
                    -- argument positions which can be used for
                    -- detagging, if it's possible (to check if it's
                    -- safe to erase)
  uniqueAuto : Bool  -- should 'auto' implicits check for uniqueness
  external : Bool -- defined externally (e.g. in a C or Scheme library)

public export
record HoleFlags where
  constructor MkHoleFlags
  implbind : Bool -- stands for an implicitly bound name

export
holeInit : Bool -> HoleFlags
holeInit b = MkHoleFlags b

public export
data Clause : Type where
     MkClause : {vars : _} ->
                (env : Env Term vars) ->
                (lhs : Term vars) -> (rhs : Term vars) -> Clause

export
covering
Show Clause where
  show (MkClause {vars} env lhs rhs)
      = show vars ++ ": " ++ show lhs ++ " = " ++ show rhs

public export
data Def : Type where
    None : Def -- Not yet defined
    Function : FnInfo ->
               (compileTime : Term [<]) ->
               (runTime : Term [<]) ->
               Maybe (List Clause) -> -- initial definition, if known
               Def -- normal function
    DCon : DataConInfo ->
           (tag : Int) -> (arity : Nat) -> Def -- data constructor
    TCon : TyConInfo -> (arity : Nat) -> Def -- type constructor
    Hole : (numlocs : Nat) -> -- Number of locals in scope at binding point
                              -- (mostly to help display)
           HoleFlags ->
           Def
    BySearch : RigCount -> (maxdepth : Nat) -> (defining : Name) -> Def
         -- ^ a name which will be found via auto-search
    -- A 'Guess' is a term which will only be well typed if the unification
    -- constraints are solved. It's promoted into a 'Function' when they are.
    -- Constraints are integer references into the current map of
    -- constraints in the UnifyState (see Core.UnifyState)
    Guess : (guess : Term [<]) ->
            (envbind : Nat) -> -- Number of things in the environment when
                               -- we guessed the term
            (constraints : List Int) -> Def

    ExternDef : (arity : Nat) -> Def -- an external primitive
    ForeignDef : (arity : Nat) ->
                 List String -> -- supported calling conventions,
                                -- e.g "C:printf,libc,stdlib.h", "scheme:display", ...
                 Def
    ImpBind : Def -- global name temporarily standing for an implicitly bound name
    UniverseLevel : Integer -> Def -- a name standing for a universe level in a Type
    -- A delayed elaboration. The elaborators themselves are stored in the
    -- unification state
    Delayed : Def

export
covering
Show Def where
  show None = "undefined"
  show (Function _ tm tm' _)
      = "Function " ++ show tm ++ "\n\tRuntime: " ++ show tm'
  show (DCon di t a)
      = "DataCon " ++ show t ++ " " ++ show a
           ++ maybe "" (\n => " (newtype by " ++ show n ++ ")")
                    (newTypeArg di)
  show (TCon ti a)
      = "TyCon " ++ " arity " ++ show a ++
        " params: " ++ show (paramPos ti) ++
        " constructors: " ++ show (datacons ti) ++
        " mutual with: " ++ show (mutWith ti) ++
        " detaggable by: " ++ show (detagBy ti)
  show (ExternDef arity) = "<external def with arity " ++ show arity ++ ">"
  show (ForeignDef a cs) = "<foreign def with arity " ++ show a ++
                           " " ++ show cs ++">"
  show (Hole _ _) = "Hole"
  show (BySearch c depth def) = "Search in " ++ show def
  show (Guess tm _ cs) = "Guess " ++ show tm ++ " when " ++ show cs
  show (UniverseLevel i) = "Universe level #" ++ show i
  show ImpBind = "Bound name"
  show Delayed = "Delayed"

export
defNameType : Def -> Maybe NameType
defNameType None = Nothing
defNameType (Function {}) = Just Func
defNameType (ExternDef {}) = Just Func
defNameType (ForeignDef {}) = Just Func
defNameType (DCon _ tag ar) = Just (DataCon tag ar)
defNameType (TCon _ ar) = Just (TyCon ar)
defNameType (Hole {}) = Just Func
defNameType (BySearch {}) = Nothing
defNameType (Guess {}) = Nothing
defNameType ImpBind = Just Bound
defNameType (UniverseLevel {}) = Nothing
defNameType Delayed = Nothing

public export
record Constructor where
  constructor MkCon
  loc : FC
  name : Name
  arity : Nat
  type : ClosedTerm

public export
data DataDef : Type where
     MkData : (tycon : Constructor) -> (datacons : List Constructor) ->
              DataDef
