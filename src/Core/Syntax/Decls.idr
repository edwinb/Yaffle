module Core.Syntax.Decls

import Core.Context
import Core.Error
import Core.Evaluate
import Core.Syntax.Raw
import Core.Typecheck.Check
import Core.Unify.State

parameters {auto c : Ref Ctxt Defs} {auto u : Ref UST UState}

  processDataCon : FC -> Name -> (Int, RawCon) -> Core Name
  processDataCon fc tycon (tag, RConDecl n rty)
      = do checkUndefined fc n
           ty <- check erased [] rty (topType fc)
           checkIsTy !(nf [] ty)
           arity <- getArity [] ty
           let dinf = MkDataConInfo Nothing
           idx <- addDef n (newDef fc n top ty Public (DCon dinf tag arity))
           pure n -- (Resolved idx)
    where
      checkIsTy : Value [] -> Core ()
      checkIsTy (VBind fc _ (Pi _ _ _ _) sc)
          = checkIsTy !(sc (VErased fc False))
      checkIsTy (VTCon fc cn _ _)
          = when (cn /= tycon) $
               throw (BadDataConType fc n tycon)
      checkIsTy _ = throw (BadDataConType fc n tycon)

  processData : FC -> RawData -> Core ()
  processData fc (RDataDecl n rty cons)
      = do checkUndefined fc n
           ty <- check erased [] rty (topType fc)
           -- Add a placeholder for the type constructor so that we can
           -- check the data constructors
           arity <- getArity [] ty
           let tinf = MkTyConInfo [] [] [] [] Nothing
           ignore $ addDef n (newDef fc n top ty Public (TCon tinf arity))
           cnames <- traverse (processDataCon fc n) (mkTags 0 cons)
           -- TODO: Deal with parameters and universe constraints
           let tinf = MkTyConInfo [] [] [] cnames Nothing
           -- Re-add with the full information
           ignore $ addDef n (newDef fc n top ty Public (TCon tinf arity))
    where
      -- I wanted to zip a Stream with a List...
      mkTags : Int -> List a -> List (Int, a)
      mkTags i [] = []
      mkTags i (x :: xs) = (i, x) :: mkTags (i + 1) xs

      checkIsType : Value [] -> Core ()
      checkIsType (VBind fc _ (Pi _ _ _ _) sc)
          = checkIsType !(sc (VErased fc False))
      checkIsType (VType fc _) = pure ()
      checkIsType _ = throw (BadTypeConType fc n)

  processTyDecl : FC -> Name -> RawC -> Core ()
  processTyDecl fc n rty
      = do checkUndefined fc n
           ty <- check erased [] rty (topType fc)
           ignore $ addDef n (newDef fc n top ty Public None)

  processDef : FC -> Name -> RawC -> Core ()
  processDef fc n rtm
      = do defs <- get Ctxt
           [(cname, i, def)] <- lookupCtxtName n (gamma defs)
                | ns => ambiguousName fc n (map fst ns)
           let None = definition def
                | _ => throw (AlreadyDefined fc n)
           tm <- check top [] rtm (type def)
           updateDef n (const (Just (Function (MkFnInfo False) tm)))

  export
  processDecl : RawDecl -> Core ()
  processDecl (RData fc d) = processData fc d
  processDecl (RTyDecl fc n ty) = processTyDecl fc n ty
  processDecl (RDef fc n def) = processDef fc n def
