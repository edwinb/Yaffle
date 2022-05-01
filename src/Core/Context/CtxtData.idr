module Core.Context.CtxtData

-- This module includes context data structures only (we need to reference
-- them in Error messages in Core.Error, and many context operations can
-- also throw errors)

-- Context entries read from TTC files will be stored as Binary, so when
-- we look them up, we have to decode them

import Core.Binary
import public Core.Context.Def
import Core.Core
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
record GlobalDef where
  constructor MkGlobalDef
  location : FC
  fullname : Name -- original unresolved name
  type : Term []
  definition : Def
  evaldef : Maybe CompiledTerm
  visibility : Visibility
  totality : Totality
  multiplicity : RigCount

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
     Coded : IntMap String -> Name -> Binary -> ContextEntry
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
    hidden : NameMap () -- Never return these

public export
record Defs where
  constructor MkDefs
  gamma : Context
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
  userHoles : NameMap Bool
     -- ^ Metavariables the user still has to fill in. In practice, that's
     -- everything with a user accessible name and a definition of Hole.
     -- The Bool says whether it was introduced in another module.
  schemeEvalLoaded : Bool

-- Label for context references
export
data Ctxt : Type where
