module Core.Check.Linear

-- Linearity checking of already typechecked/elaborated terms
-- Assumption: Terms are already type correct and we're only checking usage.
-- of local variables.
-- We must be able to complete linearity checking without reference to the
-- global context, although we are allowed to accuess the global context to
-- update quantities in hold types.

import Core.Env
import Core.Error
import Core.TT

-- List of variable usages - we'll count the contents of specific variables
-- when discharging binders, to ensure that linear names are only used once
data Usage : List Name -> Type where
     Nil : Usage vars
     (::) : Var vars -> Usage vars -> Usage vars

Show (Usage vars) where
  show xs = "[" ++ showAll xs ++ "]"
    where
      showAll : Usage vs -> String
      showAll [] = ""
      showAll [el] = show el
      showAll (x :: xs) = show x ++ ", " ++ show xs

doneScope : Usage (n :: vars) -> Usage vars
doneScope [] = []
doneScope (MkVar First :: xs) = doneScope xs
doneScope (MkVar (Later p) :: xs) = MkVar p :: doneScope xs

(++) : Usage ns -> Usage ns -> Usage ns
(++) [] ys = ys
(++) (x :: xs) ys = x :: xs ++ ys

count : Nat -> Usage ns -> Nat
count p [] = 0
count p (v :: xs)
    = if p == varIdx v then 1 + count p xs else count p xs

parameters {auto c : Ref Ctxt Defs}

  updateHoleUsage : {vars : _} ->
                    Var vars -> List (Var vars) ->
                    Term vars -> Core Bool

  lcheck : {vars : _} ->
           RigCount -> Env Term vars -> Term vars -> Core (Usage vars)
  lcheck {vars} rig env (Local fc x idx prf)
      = let b = getBinder prf env
            rigb = multiplicity b in
            do rigSafe rigb rig
               pure (used rig)
    where
      getName : {idx : _} -> (vs : List Name) -> (0 p : IsVar n idx vs) -> Name
      getName (x :: _) First = x
      getName (x :: xs) (Later p) = getName xs p

      rigSafe : RigCount -> RigCount -> Core ()
      rigSafe l r = when (l < r)
                         (throw (LinearMisuse fc (getName vars prf) l r))

      -- count the usage if we're in a linear context. If not, the usage doesn't
      -- matter
      used : RigCount -> Usage vars
      used r = if isLinear r then [MkVar prf] else []
  lcheck rig env (Ref fc nt n)
      = pure [] -- No quantity to check, and the name's quantity was checked
                -- when type checking
  lcheck rig env (Meta fc n i args) = ?todoMeta
  lcheck rig env (Bind fc x b sc) = ?todoBind
  lcheck rig env (App fc fn q arg)
      = do uf <- lcheck rig env fn
           ?todoApp
  lcheck _ _ _ = ?todo

  checkEnvUsage : {vars, done : _} ->
                  FC -> RigCount ->
                  Env Term vars -> Usage (done ++ vars) ->
                  Term (done ++ vars) ->
                  Core ()

  export
  linearCheck : {vars : _} ->
                FC -> RigCount -> Env Term vars -> Term vars -> Core ()
  linearCheck fc rig env tm
      = do used <- lcheck rig env tm
           checkEnvUsage {done = []} fc rig env used tm
