Conventions
-----------

* As far as possible, no `mutual`, always forward declare.
  + Related: no declaring in one module and defining in another
* Indent so that alpha conversion always works with a simple search and
  replace. In general this would mean starting a new line when starting a
  new level of indentation.
* Use `parameters` blocks for avoiding boilerplate when passing state around.
  If this exposes any bugs with parameter blocks in Idris 2, we must fix the
  bug rather than working around it.

Some high level decisions
-------------------------

* Let's not invent anything new unless we have absolutely no other option!
  It's more important to do what we already know as well as we possible
  can.
* Other than changing pattern matching from a top level concept to a case
  block, we'll keep other features of the theory pretty much the same. In
  particular this means:
  + RigCount is not yet first class, and we'll fix it at 0,1,unrestricted
    for now
  + No OTT just yet!
* Aim for incremental checking, rather than batch checking of files
  + In practice, I think this is about calculating dependencies of
    definitions and shouldn't be too tricky, but important to remember it
    up front at least.
