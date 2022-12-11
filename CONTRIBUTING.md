Thanks for your interest! There is still significant work to be done on the
core before accepting contributions generally, but there are a number of
TODOs throughout for which I would welcome some help. Currently these are:

* Any missing support functions for TT to be ported from existing Idris 2.
  I currently know about:
    - Core.mapTermM
* Tidy up Show instance for 'Term'
* Pretty printing of Term, TTImp and Raw syntax
* Please review the rules implemented in Core/Typecheck/Check.idr
    - Especially regarding quantities and universe levels
    - Needs fix: Test tt/unify004 will only work properly if scrutinees of
      case expressions are substituted in the environment when checking the
      right hand sides
    - Taking charge of maintenance of this typechecker would also be
      useful! It is only intended as scaffolding, but may also be helpful
      for debugging later so having a way to re-check elaborated progams
      from scratch will be useful.
* Tidy up the auto-implicits so that there are 'parameters' blocks where
  appropriate
    - I haven't always done this while porting large chunks from Idris 2,
      in the interests of making progress, but for the sake of tidiness and
      readability, it would be nice.
* Implement TTC instances
* Implement 'checkConstraints' in Core.TT.Universes. This should check
  whether the `uconstraints` are consistent and instantiate the names standing
  for universe levels as a `UniverseLevel` definition.
    - The algorithm Idris 1 uses is (probably) fine, and fast enough provided
      the queue of constraints is implemented differently!
    - For the moment it always succeeds. I am adding constraints as I work
      through unification/type checking.
* Implement an alternative conversion checker which is type-directed
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

* 'expand' needs to know whether the name it's expanding is usable in the
  current namespace. At the moment, it will expand everything.
  - So we'll also need an alternate 'expandAll' for elaborator reflection
* Port the Compiler hierarchy
  - To test, make a basic IO monad in Yaffle and try compiling and running
    some simple programs
* More tests for Yaffle
* Termination checker
  - Tests for basic operation of termination and coverage checking
* Unification details (which will come up during elaboration...):
  - Inlining things with linear quantities in the context
* Coverage checking of case blocks
  - We used to do this by knowing that functions referred to a case function.
    Now we'll need to do something slightly different, so make sure it's
    tested properly, where there's a non-covering case block inside a function
    where the top level cases are covering..
* Add universe constraints when adding data definitions
  - Find parameters + other properties we need to know elsewhere
* Universe level solver
* ???
* PROFIT

(Last updated 10th December 2022)
