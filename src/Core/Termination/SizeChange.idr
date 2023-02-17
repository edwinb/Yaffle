module Core.Termination.SizeChange

import Core.Context
import Core.Context.Log
import Core.Evaluate

import Core.Termination.References

import Libraries.Data.NameMap
import Libraries.Data.SortedMap

%default covering

Arg : Type
Arg = Int

data APos : Type where

firstArg : Arg
firstArg = 0

nextArg : Arg -> Arg
nextArg x = x + 1

initArgs : {auto a : Ref APos Arg} ->
           Nat -> Core (List (Maybe (Arg, SizeChange)))
initArgs Z = pure []
initArgs (S k)
    = do arg <- get APos
         put APos (nextArg arg)
         args' <- initArgs k
         pure (Just (arg, Same) :: args')

data Explored : Type where

-- Cached results of exploring the size change graph, so that if we visit a
-- node again, we don't have to re-explore the whole thing
SizeChanges : Type
SizeChanges = SortedMap (Name, List (Maybe Arg)) Terminating

initSCSet : SizeChanges
initSCSet = empty

-- Traverse the size change graph. When we reach a point we've seen before,
-- at least one of the arguments must have got smaller, otherwise it's
-- potentially non-terminating
checkSC : {auto a : Ref APos Arg} ->
          {auto c : Ref Ctxt Defs} ->
          {auto e : Ref Explored SizeChanges} ->
          Defs ->
          Name -> -- function we're checking
          List (Maybe (Arg, SizeChange)) -> -- functions arguments and change
          List (Name, List (Maybe Arg)) -> -- calls we've seen so far
          Core Terminating
checkSC defs f args path
   = do exp <- get Explored
        log "totality.termination.sizechange" 7 $ "Checking Size Change Graph: " ++ show !(toFullNames f)
        let pos = (f, map (map Builtin.fst) args)
        case lookup pos exp of
             Just done => pure done -- already explored this bit of tree
             Nothing =>
                if pos `elem` path
                   then do log "totality.termination.sizechange.inPath" 8 $ "Checking arguments: " ++ show !(toFullNames f)
                           res <- toFullNames $ checkDesc (mapMaybe (map Builtin.snd) args) path
                           put Explored (insert pos res exp)
                           pure res
                   else case !(lookupCtxtExact f (gamma defs)) of
                             Nothing => do log "totality.termination.sizechange.isTerminating" 8 $ "Size Change Graph is Terminating for: " ++ show !(toFullNames f)
                                           pure IsTerminating
                             Just def => do log "totality.termination.sizechange.needsChecking" 8 $ "Size Change Graph needs traversing: " ++ show !(toFullNames f)
                                            continue (sizeChange def) (pos :: path)
  where
    -- Look for something descending in the list of size changes
    checkDesc : List SizeChange -> List (Name, List (Maybe Arg)) -> Terminating
    checkDesc [] path = NotTerminating (RecPath (reverse (map fst path)))
    checkDesc (Smaller :: _) _ = IsTerminating
    checkDesc (_ :: xs) path = checkDesc xs path

    getPos : forall a . List a -> Nat -> Maybe a
    getPos [] _ = Nothing
    getPos (x :: xs) Z = Just x
    getPos (x :: xs) (S k) = getPos xs k

    updateArg : SizeChange -> Maybe (Arg, SizeChange) -> Maybe (Arg, SizeChange)
    updateArg c Nothing = Nothing
    updateArg c arg@(Just (i, Unknown)) = arg
    updateArg Unknown (Just (i, _)) = Just (i, Unknown)
    updateArg c (Just (i, Same)) = Just (i, c)
    updateArg c arg = arg

    mkArgs : List (Maybe (Nat, SizeChange)) -> List (Maybe (Arg, SizeChange))
    mkArgs [] = []
    mkArgs (Nothing :: xs) = Nothing :: mkArgs xs
    mkArgs (Just (pos, c) :: xs)
        = case getPos args pos of
               Nothing => Nothing :: mkArgs xs
               Just arg => updateArg c arg :: mkArgs xs

    checkCall : List (Name, List (Maybe Arg)) -> SCCall -> Core Terminating
    checkCall path sc
        = do Just gdef <- lookupCtxtExact (fnCall sc) (gamma defs)
                  | Nothing => pure IsTerminating -- nothing to check
             let Unchecked = isTerminating (totality gdef)
                  | IsTerminating => pure IsTerminating
                  | _ => pure (NotTerminating (BadCall [fnCall sc]))
             log "totality.termination.sizechange.checkCall" 8 $
                "CheckCall Size Change Graph: " ++ show !(toFullNames (fnCall sc))
             term <- checkSC defs (fnCall sc) (mkArgs (fnArgs sc)) path
             let inpath = fnCall sc `elem` map fst path
             if not inpath
                then case term of
                       NotTerminating (RecPath _) =>
                          -- might have lost information while assuming this
                          -- was mutually recursive, so start again with new
                          -- arguments (that is, where we'd start if the
                          -- function was the top level thing we were checking)
                          do log "totality.termination.sizechange.checkCall.inPathNot.restart" 9 $ "ReChecking Size Change Graph: " ++ show !(toFullNames (fnCall sc))
                             args' <- initArgs (length (fnArgs sc))
                             t <- checkSC defs (fnCall sc) args' path
                             setTerminating emptyFC (fnCall sc) t
                             pure t
                       t => do log "totality.termination.sizechange.checkCall.inPathNot.return" 9 $ "Have result: " ++ show !(toFullNames (fnCall sc))
                               pure t
                else do log "totality.termination.sizechange.checkCall.inPath" 9 $ "Have Result: " ++ show !(toFullNames (fnCall sc))
                        pure term

    getWorst : Terminating -> List Terminating -> Terminating
    getWorst term [] = term
    getWorst term (IsTerminating :: xs) = getWorst term xs
    getWorst term (Unchecked :: xs) = getWorst Unchecked xs
    getWorst term (bad :: xs) = bad

    continue : List SCCall -> List (Name, List (Maybe Arg)) -> Core Terminating
    continue scs path
        = do allTerm <- traverse (checkCall path) scs
             pure (getWorst IsTerminating allTerm)

export
calcTerminating : {auto c : Ref Ctxt Defs} ->
                  FC -> Name -> Core Terminating
calcTerminating loc n
    = do defs <- get Ctxt
         log "totality.termination.calc" 7 $ "Calculating termination: " ++ show !(toFullNames n)
         case !(lookupCtxtExact n (gamma defs)) of
              Nothing => undefinedName loc n
              Just def =>
                case !(totRefs defs (keys (refersTo def))) of
                     IsTerminating =>
                        do let ty = type def
                           a <- newRef APos firstArg
                           args <- initArgs !(getArity [<] ty)
                           e <- newRef Explored initSCSet
                           checkSC defs n args []
                     bad => pure bad
