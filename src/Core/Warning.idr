module Core.Warning

import Core.Binary
import public Core.Core
import public Core.Env
import public Core.TT

import Data.List1

public export
data Warning : Type where
     ParserWarning : FC -> String -> Warning
     UnreachableClause : {vars : _} ->
                         FC -> Env Term vars -> Term vars -> Warning
     ShadowingGlobalDefs : FC -> List1 (String, List1 Name) -> Warning
     ||| First FC is type
     ||| @ shadowed list of names which are shadowed,
     |||   where they originally appear
     |||   and where they are shadowed
     ShadowingLocalBindings : FC -> (shadowed : List1 (String, FC, FC)) -> Warning
     ||| A warning about a deprecated definition. Supply an FC and Name to
     ||| have the documentation for the definition printed with the warning.
     Deprecated : String -> Maybe (FC, Name) -> Warning
     GenericWarn : String -> Warning

%name Warning wrn

-- Simplest possible display - higher level languages should unelaborate names
-- and display annotations appropriately

export
Show Warning where
    show (ParserWarning _ msg) = msg
    show (UnreachableClause _ _ _) = ":Unreachable clause"
    show (ShadowingGlobalDefs _ _) = ":Shadowing names"
    show (ShadowingLocalBindings _ _) = ":Shadowing names"
    show (Deprecated name _) = ":Deprecated " ++ name
    show (GenericWarn msg) = msg

-- Not fully correct, see e.g. `UnreachableClause` where we don't check the
-- Envs & Terms because we don't yet have equality instances for these
export
Eq Warning where
  ParserWarning fc1 x1 == ParserWarning fc2 x2 = fc1 == fc2 && x1 == x2
  UnreachableClause fc1 rho1 s1 == UnreachableClause fc2 rho2 s2 = fc1 == fc2
  ShadowingGlobalDefs fc1 xs1 == ShadowingGlobalDefs fc2 xs2 = fc1 == fc2 && xs1 == xs2
  ShadowingLocalBindings fc1 xs1 == ShadowingLocalBindings fc2 xs2 = fc1 == fc2 && xs1 == xs2
  Deprecated x1 y1 == Deprecated x2 y2 = x1 == x2 && y1 == y2
  GenericWarn x1 == GenericWarn x2 = x1 == x2
  _ == _ = False
