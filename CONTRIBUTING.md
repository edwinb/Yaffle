Thanks for your interest! There is still significant work to be done on the
core before accepting contributions generally, but there are a number of
small TODOs throughout for which I would welcome some help. Currently
these are:

* Any missing support functions for TT to be ported from existing Idris 2
    - I will add these as they are needed, but it's even better if they're
      already done :). Mostly they'll be the same, with the addition of
      case alternatives. Experience so far is that case alternatives in the
      new representation are easier to process...
* Tidy up Show instance for 'Term'
* Pretty printing of Term and TTImp
* Do the parser for Core Syntax properly.
    - It is just a quick S-expression based hack to allow setting up testing,
      experimentation, etc.
    - Also, it would be nice to have a reasonably tidy parser for TTImp syntax,
      when the time comes to write an elaborator.
* Make sure the 'Libraries' modules are consistent with CONVENTIONS.md

(Last updated 22nd April 2022)
