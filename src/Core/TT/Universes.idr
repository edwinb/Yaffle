module Core.TT.Universes

import Core.Context

parameters {auto c : Ref Ctxt Defs}
  export
  addConstraint : UConstraint -> CoreE err ()
  addConstraint c
      = do defs <- get Ctxt
           put Ctxt ({ uconstraints $= (c ::) } defs)

  -- Check constraints are consistent and instantiate names as universe levels
  export
  checkConstraints : Core ()
  checkConstraints = pure () -- TODO
