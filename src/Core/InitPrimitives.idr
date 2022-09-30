module Core.InitPrimitives

import Core.Context
import Core.Core
import Core.FC
import Core.Primitives
import Core.TT

import Data.Nat
import Data.Vect

mkFn : (i : Int) ->
       (todo : Nat) -> PrimFn (todo + done) ->
       Vect done (Var vars) -> Term vars
mkFn i Z op args
    = PrimOp EmptyFC op (reverse (map mkLoc args))
  where
    mkLoc : Var vars -> Term vars
    mkLoc (MkVar p) = Local EmptyFC Nothing _ p
mkFn i (S k) op args
    = Bind EmptyFC (MN "arg" i)
           (Lam EmptyFC RigW Explicit (Erased EmptyFC False))
           (mkFn (i + 1) k
                 (rewrite sym (plusSuccRightSucc k done) in op)
                 (MkVar First :: map later args))

mkPrim : (arity : Nat) -> PrimFn arity -> Term [<]
mkPrim a op = mkFn 0 a (rewrite plusZeroRightNeutral a in op) []

addPrim : Ref Ctxt Defs =>
          Prim -> CoreE err ()
addPrim p
    = do let primdef = newDef EmptyFC (opName (fn p)) RigW [<]
                              (type p) Public
                              (Function (MkFnInfo NotHole False False)
                                        (mkPrim (arity p) (fn p)))
         ignore $ addDef (opName (fn p)) primdef

export
addPrimitives : Ref Ctxt Defs =>
                CoreE err ()
addPrimitives = traverse_ addPrim allPrimitives
