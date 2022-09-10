Thanks for your interest! There is still significant work to be done on the
core before accepting contributions generally, but there are a number of
TODOs throughout for which I would welcome some help. Currently these are:

* Please review the rules implemented in Core/Typecheck/Check.idr
    - Especially regarding quantities and universe levels
* Tidy up the auto-implicits so that there are 'parameters' blocks where
  appropriate
    - I haven't always done this while porting large chunks from Idris 2,
      in the interests of making progress, but for the sake of tidiness and
      readability, it would be nice.
* Some things which have changed in Idris 2 should ideally be changed here
    - Most obviously: PrT/PrimType in the TT structure
* Any missing support functions for TT to be ported from existing Idris 2
    - I will add these as they are needed, but it's even better if they're
      already done :). Mostly they'll be the same, with the addition of
      case alternatives. Experience so far is that case alternatives in the
      new representation are easier to process...
* Implement TTC instances
* Implement 'checkConstraints' in Core.TT.Universes. This should check
  whether the `uconstraints` are consistent and instantiate the names standing
  for universe levels as a `UniverseLevel` definition.
    - The algorithm Idris 1 uses is (probably) fine, and fast enough provided
      the queue of constraints is implemented differently!
    - For the moment it always succeeds. I am adding constraints as I work
      through unification/type checking.
* Implement an alternative conversion checker which is type-directed
* Tidy up Show instance for 'Term'
* Pretty printing of Term, TTImp and Raw syntax
* Do the parser for Core Syntax properly.
    - It is just a quick hack to allow setting up testing, experimentation, etc.
    - It would be still be nice if it got past the totality checker
    - Also, it would be nice to have a reasonably tidy parser for TTImp syntax,
      when the time comes to write an elaborator.
* Make sure the 'Libraries' modules are consistent with CONVENTIONS.md
* (Complicated!): Add a feature to Idris 2 which dumps raw TT in a form readable
  by Yaffle's raw type checker.
    - Useful for testing Yaffle's evaluator and performance, also as a check
      that the typechecker works.
    - I will leave the design up to whoever has a go at this.

edwinb's next steps:

* Continue TTImp elaborator
* Unification details (which will come up during elaboration...):
  - Inlining things with linear quantities in the context
  - We don't need 'inlineOnly' in the context any more, so remove once
    unification works and inlining metavariables works as it should
  - Implement auto-implicit search
* Implement/port the missing interfaces for TTC/HasNames
* Check TTCs work
  - Note on string table: Sometimes we shortcut TTC loading (when all we're
    interested in is which modules it imports), in which case we'd not actually
    want to process the string table pointlessly. So it may be that we want to
    process it lazily, and use the RawString instance for any Strings before
    the actual program data
* Add universe constraints when adding data definitions
  - Find parameters + other properties we need to know elsewhere
* Universe level solver
* Question: Should Errors use 'Value' rather than 'Term'?
* ???
* PROFIT

(Last updated 5th August 2022)
