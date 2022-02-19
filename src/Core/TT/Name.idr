module Core.TT.Name

import public Core.TT.Namespace

||| A username has some structure
public export
data UserName : Type where
  Basic : String -> UserName -- default name constructor       e.g. map
  Field : String -> UserName -- field accessor                 e.g. .fst
  Underscore : UserName      -- no name                        e.g. _

public export
data Name : Type where
     NS : Namespace -> Name -> Name -- in a namespace
     UN : UserName -> Name -- user defined name
     MN : String -> Int -> Name -- machine generated name
     PV : Name -> Int -> Name -- pattern variable name; int is the resolved function id
     DN : String -> Name -> Name -- a name and how to display it
     WithBlock : String -> Int -> Name -- with block nested in (resolved) name
     Resolved : Int -> Name -- resolved, index into context

export
Show UserName where
  show (Basic n) = n
  show (Field n) = "." ++ n
  show Underscore = "_"

export
Show Name where
  show (NS ns n@(UN (Field _))) = show ns ++ ".(" ++ show n ++ ")"
  show (NS ns n) = show ns ++ "." ++ show n
  show (UN x) = show x
  show (MN x y) = "{" ++ x ++ ":" ++ show y ++ "}"
  show (PV n d) = "{P:" ++ show n ++ ":" ++ show d ++ "}"
  show (DN str n) = str
  show (WithBlock outer i) = "with block in " ++ outer
  show (Resolved x) = "$resolved" ++ show x
