module Core.Search

import Core.Core
import Core.Error

import Libraries.Data.Tap

namespace Search

  public export
  Search : Type -> Type
  Search = Tap Core

  export %hint
  functor : Functor Search
  functor = (the (forall m. Functor m -> Functor (Tap m)) %search) CORE

  export
  traverse : (a -> Core b) -> Search a -> Core (Search b)
  traverse = Tap.traverse @{CORE}

  export
  filter : (a -> Bool) -> Search a -> Core (Search a)
  filter = Tap.filter @{CORE}
