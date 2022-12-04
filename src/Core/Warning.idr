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
