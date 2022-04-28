Thanks for your interest! There is still significant work to be done on the
core before accepting contributions generally, but there are a number of
TODOs throughout for which I would welcome some help. Currently these are:

* Any missing support functions for TT to be ported from existing Idris 2
    - I will add these as they are needed, but it's even better if they're
      already done :). Mostly they'll be the same, with the addition of
      case alternatives. Experience so far is that case alternatives in the
      new representation are easier to process...
* Implement 'checkConstraints' in Core.TT.Universes. This should check
  whether the `uconstraints` are consistent and instantiate the names standing
  for universe levels as a `UniverseLevel` definition.
    - The algorithm Idris 1 uses is (probably) fine, and fast enough provided
      the queue of constraints is implemented differently!
    - For the moment it always succeeds. I am adding constraints as I work
      through unification/type checking.
* Tidy up Show instance for 'Term'
* Pretty printing of Term and TTImp
* Do the parser for Core Syntax properly.
    - It is just a quick S-expression based hack to allow setting up testing,
      experimentation, etc.
    - Also, it would be nice to have a reasonably tidy parser for TTImp syntax,
      when the time comes to write an elaborator.
* Make sure the 'Libraries' modules are consistent with CONVENTIONS.md

edwinb's next steps:

* Finish conversion checking
* Finish parser for raw terms
* Set up a testing system as early as possible!
* Write a typechecker for raw terms
* Change index of Terms from List Name to SnocList Name
* Write a linearity checker for typechecked terms
  - find out where we need to cache quantities in applications
* Implement unification
* ???
* PROFIT

(Last updated 22nd April 2022)
