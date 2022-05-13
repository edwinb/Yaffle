Thanks for your interest! There is still significant work to be done on the
core before accepting contributions generally, but there are a number of
TODOs throughout for which I would welcome some help. Currently these are:

* Please review the rules implement in Core/Typecheck/Check.idr
    - Especially regarding quantities and universe levels
* Any missing support functions for TT to be ported from existing Idris 2
    - I will add these as they are needed, but it's even better if they're
      already done :). Mostly they'll be the same, with the addition of
      case alternatives. Experience so far is that case alternatives in the
      new representation are easier to process...
* Finish 'matchVars' in Core.Typecheck.Support.
    - This is for finding the variables to substitute in types when checking
      simple case blocks. Current state is fine for the basic test cases,
      and we won't typically use this typechecker in elaboration, but we will
      need it for debugging/rechecking results of elaboration.
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

* Add universe constraints when adding data definitions
  - Find parameters + other properties we need to know elsewhere
* Add metavariables to RawTT
  - Needed for unification, and also because they are one of the most
    interesting things we need to deal with in linearity checking.
* Write a linearity checker for typechecked terms
  - find out where we need to cache quantities in applications
* Add test framework with existing small tt files
* Change index of Terms from List Name to SnocList Name
* Universe level solver
* Implement HasNames so we can do resolved names
* Implement unification
* Add holes to Raw TT (to try unification in the simplest possible setting)
* ???
* PROFIT

(Last updated 13th May 2022)
