module Core.Context.CtxtData

-- This module includes context data structures only (we need to reference
-- them in Error messages in Core.Error, and many context operations can
-- also throw errors)

-- Context entries read from TTC files will be stored as Binary, so when
-- we look them up, we have to decode them

import Core.Binary
import public Core.Context.Def
import Core.CompileExpr
import Core.Core
import Core.Warning
import Core.Options
import Core.TT

import Libraries.Data.IntMap
import Libraries.Data.IOArray
import Libraries.Data.NameMap
import Libraries.Data.UserNameMap

import Libraries.Utils.Scheme

public export
record CompiledTerm where
  constructor MkCompiledTerm
  evalTC : SchemeObj Write -- for typechecking, so 'export' names blocked
  evalAll : SchemeObj Write -- for evaluation at the REPL, so compile all fully

public export
data NoMangleDirective : Type where
    CommonName : String -> NoMangleDirective
    BackendNames : List (String, String) -> NoMangleDirective

public export
data DefFlag
    = Inline
    | NoInline
    | ||| A definition has been marked as deprecated
      Deprecate
    | Invertible -- assume safe to cancel arguments in unification
    | Overloadable -- allow ad-hoc overloads
    | TCInline -- always inline before totality checking
         -- (in practice, this means it's reduced in 'normaliseHoles')
         -- This means the function gets inlined when calculating the size
         -- change graph, but otherwise not. It's only safe if the function
         -- being inlined is terminating no matter what, and is really a bit
         -- of a hack to make sure interface dictionaries are properly inlined
         -- (otherwise they look potentially non terminating) so use with
         -- care!
    | SetTotal TotalReq
    | BlockedHint -- a hint, but blocked for the moment (so don't use)
    | Macro
    | PartialEval (List (Name, Nat)) -- Partially evaluate on completing defintion.
         -- This means the definition is standing for a specialisation so we
         -- should evaluate the RHS, with reduction limits on the given names,
         -- and ensure the name has made progress in doing so (i.e. has reduced
         -- at least once)
    | AllGuarded -- safe to treat as a constructor for the purposes of
         -- productivity checking. All clauses are guarded by constructors,
         -- and there are no other function applications
    | ConType ConInfo
         -- Is it a special type of constructor, e.g. a nil or cons shaped
         -- thing, that can be compiled specially?
    | Identity Nat
         -- Is it the identity function at runtime?
         -- The nat represents which argument the function evaluates to
    | NoMangle NoMangleDirective
         -- use the user provided name directly (backend, name)

export
Eq DefFlag where
    (==) Inline Inline = True
    (==) NoInline NoInline = True
    (==) Deprecate Deprecate = True
    (==) Invertible Invertible = True
    (==) Overloadable Overloadable = True
    (==) TCInline TCInline = True
    (==) (SetTotal x) (SetTotal y) = x == y
    (==) BlockedHint BlockedHint = True
    (==) Macro Macro = True
    (==) (PartialEval x) (PartialEval y) = x == y
    (==) AllGuarded AllGuarded = True
    (==) (ConType x) (ConType y) = x == y
    (==) (Identity x) (Identity y) = x == y
    (==) (NoMangle _) (NoMangle _) = True
    (==) _ _ = False

export
Show DefFlag where
  show Inline = "inline"
  show NoInline = "noinline"
  show Deprecate = "deprecate"
  show Invertible = "invertible"
  show Overloadable = "overloadable"
  show TCInline = "tcinline"
  show (SetTotal x) = show x
  show BlockedHint = "blockedhint"
  show Macro = "macro"
  show (PartialEval _) = "partialeval"
  show AllGuarded = "allguarded"
  show (ConType ci) = "contype " ++ show ci
  show (Identity x) = "identity " ++ show x
  show (NoMangle _) = "nomangle"

public export
data SizeChange = Smaller | Same | Unknown

export
Show SizeChange where
  show Smaller = "Smaller"
  show Same = "Same"
  show Unknown = "Unknown"

export
Eq SizeChange where
  Smaller == Smaller = True
  Same == Same = True
  Unknown == Unknown = True
  _ == _ = False

public export
record SCCall where
     constructor MkSCCall
     fnCall : Name -- Function called
     fnArgs : List (Maybe (Nat, SizeChange))
        -- relationship to arguments of calling function; argument position
        -- (in the calling function), and how its size changed in the call.
        -- 'Nothing' if it's not related to any of the calling function's
        -- arguments

export
Show SCCall where
  show c = show (fnCall c) ++ ": " ++ show (fnArgs c)

export
Eq SCCall where
  x == y = fnCall x == fnCall y && fnArgs x == fnArgs y

public export
record GlobalDef where
  constructor MkGlobalDef
  location : FC
  fullname : Name -- original unresolved name
  type : Term [<]
  eraseArgs : List Nat -- which argument positions to erase at runtime
  safeErase : List Nat -- which argument positions are safe to assume
                       -- erasable without 'dotting', because their types
                       -- are collapsible relative to non-erased arguments
  specArgs : List Nat -- arguments to specialise by
  inferrable : List Nat -- arguments which can be inferred from elsewhere in the type
  multiplicity : RigCount
  localVars : List Name -- environment name is defined in
  visibility : Visibility
  totality : Totality
  flags : List DefFlag
  refersToM : Maybe (NameMap Bool)
  refersToRuntimeM : Maybe (NameMap Bool)
  invertible : Bool -- for an ordinary definition, is it invertible in unification
  definition : Def
  compexpr : Maybe CDef
  namedcompexpr : Maybe NamedDef
  sizeChange : List SCCall
  evaldef : Maybe CompiledTerm

export
TTC GlobalDef where
  toBuf d = ?todo1
  fromBuf = ?todo2

-- Label for array references
export
data Arr : Type where

-- A context entry. If it's never been looked up, we haven't decoded the
-- binary blob yet, so decode it first time
public export
data ContextEntry : Type where
     Coded : IntMap String -> Name -> Binary Read -> ContextEntry
     Decoded : GlobalDef -> ContextEntry

public export
data PossibleName : Type where
     Direct : Name -> Int -> PossibleName -- full name and resolved name id
     Alias : Name -> -- aliased name (from "import as")
             Name -> Int -> -- real full name and resolved name, as above
             PossibleName

-- All the GlobalDefs. We can only have one context, because name references
-- point at locations in here, and if we have more than one the indices won't
-- match up. So, this isn't polymorphic.
public export
record Context where
    constructor MkContext
    firstEntry : Int -- First entry in the current source file
    nextEntry : Int
    stringTable : StringTable -- map from Strings to Ints, for writing TTC more efficiently
                              -- This is kept up to date when writing to the TTC
    -- Map from full name to its position in the context
    resolvedAs : NameMap Int
    -- Map from usernames to all the possible names in all namespaces
    possibles : UserNameMap (List PossibleName)
    -- Reference to the actual content, indexed by Int
    content : Ref Arr (IOArray ContextEntry)
    -- Branching depth, in a backtracking elaborator. 0 is top level; at lower
    -- levels we need to stage updates rather than add directly to the
    -- 'content' store
    branchDepth : Nat
    -- Things which we're going to add, if this branch succeeds
    staging : IntMap ContextEntry

    -- Namespaces which are visible (i.e. have been imported)
    -- This only matters during evaluation and type checking, to control
    -- access in a program - in all other cases, we'll assume everything is
    -- visible
    visibleNS : List Namespace
    inlineOnly : Bool -- only return things with the 'alwaysReduce' flag
                      -- FIXME: We shouldn't need this any more due to new
                      -- glued representation, so remove it after implemeting
                      -- unification
    hidden : NameMap () -- Never return these

-- Rewrite rules, applied after type checking, for runtime code only
-- LHS and RHS must have the same type, but we don't (currently) require that
-- the result still type checks (which might happen e.g. if transforming to a
-- faster implementation with different behaviour)
-- (Q: Do we need the 'Env' here? Usually we end up needing an 'Env' with a
-- 'NF but we're working with terms rather than values...)
public export
data Transform : Type where
     MkTransform : {vars : _} ->
                   Name -> -- name for identifying the rule
                   Env Term vars -> Term vars -> Term vars -> Transform

export
getFnName : Transform -> Maybe Name
getFnName (MkTransform _ _ app _)
    = case getFn app of
           Ref _ _ fn => Just fn
           _ => Nothing

public export
record Defs where
  constructor MkDefs
  gamma : Context
  mutData : List Name -- Currently declared but undefined data types
  uconstraints : List UConstraint
  nextUVar : Int
  currentNS : Namespace -- namespace for current definitions
  nestedNS : List Namespace -- other nested namespaces we can look in
  options : Options
  toSave : NameMap ()
  nextTag : Int
  typeHints : NameMap (List (Name, Bool))
     -- ^ a mapping from type names to hints (and a flag setting whether it's
     -- a "direct" hint). Direct hints are searched first (as part of a group)
     -- the indirect hints. Indirect hints, in practice, are used to find
     -- instances of parent interfaces, and we don't search these until we've
     -- tried to find a direct result via a constructor or a top level hint.
  autoHints : NameMap Bool
     -- ^ global search hints. A mapping from the hint name, to whether it is
     -- a "default hint". A default hint is used only if all other attempts
     -- to search fail (this flag is really only intended as a mechanism
     -- for defaulting of literals)
  openHints : NameMap ()
     -- ^ currently open global hints; just for the rest of this module (not exported)
     -- and prioritised
  localHints : NameMap ()
     -- ^ Hints defined in the current environment
  saveTypeHints : List (Name, Name, Bool)
     -- We don't look up anything in here, it's merely for saving out to TTC.
     -- We save the hints in the 'GlobalDef' itself for faster lookup.
  saveAutoHints : List (Name, Bool)
  transforms : NameMap (List Transform)
     -- ^ A mapping from names to transformation rules which update applications
     -- of that name
  saveTransforms : List (Name, Transform)
  namedirectives : NameMap (List String)
  ifaceHash : Int
  importHashes : List (Namespace, Int)
     -- ^ interface hashes of imported modules
  imported : List (ModuleIdent, Bool, Namespace)
     -- ^ imported modules, whether to rexport, as namespace
  allImported : List (String, (ModuleIdent, Bool, Namespace))
     -- ^ all imported filenames/namespaces, just to avoid loading something
     -- twice unnecessarily (this is a record of all the things we've
     -- called 'readFromTTC' with, in practice)
  cgdirectives : List (CG, String)
     -- ^ Code generator directives, which are free form text and thus to
     -- be interpreted however the specific code generator requires
  toCompileCase : List Name
     -- ^ Names which need to be compiled to run time case trees
  incData : List (CG, String, List String)
     -- ^ What we've compiled incrementally for this module: codegen,
     -- object file, any additional CG dependent data (e.g. linker flags)
  allIncData : List (CG, List String, List String)
     -- ^ Incrementally compiled files for all imports. Only lists CGs for
     -- while all modules have associated incremental compile data
  toIR : NameMap ()
     -- ^ Names which need to be compiled to IR at the end of processing
     -- the current module
  userHoles : NameMap Bool
     -- ^ Metavariables the user still has to fill in. In practice, that's
     -- everything with a user accessible name and a definition of Hole.
     -- The Bool says whether it was introduced in another module.
  warnings : List Warning
       -- ^ as yet unreported warnings
  schemeEvalLoaded : Bool

-- Label for context references
export
data Ctxt : Type where
