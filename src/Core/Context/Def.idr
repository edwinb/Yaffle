module Core.Context.Def

-- This module includes:
-- * The forms of definition (function, data type etc)

import Core.TT

public export
record FnInfo where
  constructor MkFnInfo
  alwaysReduce : Bool -- Always reduce - typically for inlinable metavar sulutions

public export
record DataConInfo where
  constructor MkDataConInfo
  newTypeArg : Maybe (Bool, Nat)
               -- if it's the only constructor, and only one argument is
               -- non-Rig0, flag it here.
               -- The Nat is the unerased argument position.
               -- The Bool is 'True' if there is no %World token in the
               -- structure, which means it is safe to completely erase
               -- when pattern matching (otherwise we still have to ensure
               -- that the value is inspected, to make sure external effects
               -- happen)

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

public export
data Def : Type where
    None : Def -- Not yet defined
    Function : FnInfo -> Term [] -> Def -- normal function
    DCon : DataConInfo ->
           (tag : Int) -> (arity : Nat) -> Def -- data constructor
    TCon : TyConInfo ->
           (tag : Int) -> (arity : Nat) -> Def -- type constructor
    Hole : (numlocs : Nat) -> -- Number of locals in scope at binding point
                              -- (mostly to help display)
           Def
    BySearch : RigCount -> (maxdepth : Nat) -> (defining : Name) -> Def
         -- ^ a name which will be found via auto-search
    -- Constraints are integer references into the current map of
    -- constraints in the UnifyState (see Core.UnifyState)
    Guess : (guess : Term []) ->
            (envbind : Nat) -> -- Number of things in the environment when
                               -- we guessed the term
            (constraints : List Int) -> Def

    ExternDef : (arity : Nat) -> Def -- an external primitive
    ForeignDef : (arity : Nat) ->
                 List String -> -- supported calling conventions,
                                -- e.g "C:printf,libc,stdlib.h", "scheme:display", ...
                 Def
    Builtin : {arity : Nat} -> PrimFn arity -> Def -- primitive
    ImpBind : Def -- global name temporarily standing for an implicitly bound name
    UniverseLevel : Integer -> Def -- a name standing for a universe level in a Type
    -- A delayed elaboration. The elaborators themselves are stored in the
    -- unification state
    Delayed : Def
