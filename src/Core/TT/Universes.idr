module Core.TT.Universes

import Core.Context

parameters {auto c : Ref Ctxt Defs}
  export
  addConstraint : UConstraint -> CoreE err ()
  addConstraint c
      = do defs <- get Ctxt
           put Ctxt ({ uconstraints $= (c ::) } defs)

  -- Generate the next universe variable
  export
  uniVar : FC -> Core Name
  uniVar fc
      = do defs <- get Ctxt
           let n = MN "u" (nextUVar defs)
           put Ctxt ({nextUVar $= (1+) } defs)
           idx <- addDef n (newDef fc n erased [<] (Erased fc Placeholder) Public None)
           pure (Resolved idx)

  -- Check constraints are consistent and instantiate names as universe levels
  export
  checkConstraints : Core ()
  checkConstraints = pure () -- TODO
