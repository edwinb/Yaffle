module Core.InitPrimitives

import Compiler.CompileExpr

import Core.Context
import Core.Core
import Core.FC
import Core.Primitives
import Core.TT

import Data.Nat
import Data.Vect

mkFn : {done : _} ->
       (i : Int) ->
       (todo : Nat) -> PrimFn (todo + done) ->
       Vect done (Var vars) -> Term vars
mkFn i Z op args
    = PrimOp EmptyFC op (reverse (map mkLoc args))
  where
    mkLoc : Var vars -> Term vars
    mkLoc (MkVar p) = Local EmptyFC _ p
mkFn i (S k) op args
    = Bind EmptyFC (MN "arg" i)
           (Lam EmptyFC RigW Explicit (Erased EmptyFC Placeholder))
           (mkFn (i + 1) k
                 (rewrite sym (plusSuccRightSucc k done) in op)
                 (MkVar First :: map later args))

mkPrim : (arity : Nat) -> PrimFn arity -> Term [<]
mkPrim a op = mkFn 0 a (rewrite plusZeroRightNeutral a in op) []

addPrim : Ref Ctxt Defs =>
          Prim -> Core ()
addPrim p
    = do let fndef = mkPrim (arity p) (fn p)
         let primdef = newDef EmptyFC (opName (fn p)) RigW [<]
                              (type p) Public
                              (Function (MkFnInfo NotHole False False)
                                        fndef fndef Nothing)
         ignore $ addDef (opName (fn p)) primdef
         compileDef (opName (fn p))

export
addPrimitives : Ref Ctxt Defs =>
                Core ()
addPrimitives = traverse_ addPrim allPrimitives
