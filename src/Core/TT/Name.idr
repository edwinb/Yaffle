module Core.TT.Name

import public Core.TT.Namespace

import Data.String
import Decidable.Equality

import Libraries.Data.String.Extra
import Libraries.Text.PrettyPrint.Prettyprinter
import Libraries.Text.PrettyPrint.Prettyprinter.Util

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

export
Pretty UserName where
  pretty (Basic n) = pretty n
  pretty (Field n) = "." <+> pretty n
  pretty Underscore = "_"

export
Pretty Name where
  pretty (NS ns n@(UN (Field _))) = pretty ns <+> dot <+> parens (pretty n)
  pretty (NS ns n) = pretty ns <+> dot <+> pretty n
  pretty (UN x) = pretty x
  pretty (MN x y) = braces (pretty x <+> colon <+> pretty y)
  pretty (PV n d) = braces (pretty 'P' <+> colon <+> pretty n <+> colon <+> pretty d)
  pretty (DN str _) = pretty str
  pretty (WithBlock outer _) = reflow "with block in" <++> pretty outer
  pretty (Resolved x) = pretty "$resolved" <+> pretty x

export
Eq UserName where
  (==) (Basic x) (Basic y) = x == y
  (==) (Field x) (Field y) = x == y
  (==) Underscore Underscore = True
  (==) _ _ = False


export
Eq Name where
    (==) (NS ns n) (NS ns' n') = n == n' && ns == ns'
    (==) (UN x) (UN y) = x == y
    (==) (MN x y) (MN x' y') = y == y' && x == x'
    (==) (PV x y) (PV x' y') = x == x' && y == y'
    (==) (DN _ n) (DN _ n') = n == n'
    (==) (WithBlock x y) (WithBlock x' y') = y == y' && x == x'
    (==) (Resolved x) (Resolved x') = x == x'
    (==) _ _ = False

usernameTag : UserName -> Int
usernameTag (Basic _) = 0
usernameTag (Field _) = 2
usernameTag Underscore = 3

export
Ord UserName where
  compare (Basic x) (Basic y) = compare x y
  compare (Field x) (Field y) = compare x y
  compare Underscore Underscore = EQ
  compare x y = compare (usernameTag x) (usernameTag y)

nameTag : Name -> Int
nameTag (NS _ _) = 0
nameTag (UN _) = 1
nameTag (MN _ _) = 2
nameTag (PV _ _) = 3
nameTag (DN _ _) = 4
nameTag (WithBlock _ _) = 5
nameTag (Resolved _) = 6

export
Ord Name where
    compare (NS x y) (NS x' y')
        = case compare y y' of -- Compare base name first (more likely to differ)
               EQ => compare x x'
               -- Because of the terrible way Idris 1 compiles 'case', this
               -- is actually faster than just having 't => t'...
               GT => GT
               LT => LT
    compare (UN x) (UN y) = compare x y
    compare (MN x y) (MN x' y')
        = case compare y y' of
               EQ => compare x x'
               GT => GT
               LT => LT
    compare (PV x y) (PV x' y')
        = case compare y y' of
               EQ => compare x x'
               GT => GT
               LT => LT
    compare (DN _ n) (DN _ n') = compare n n'
    compare (WithBlock x y) (WithBlock x' y')
        = case compare y y' of
               EQ => compare x x'
               GT => GT
               LT => LT
    compare (Resolved x) (Resolved y) = compare x y

    compare x y = compare (nameTag x) (nameTag y)


export
userNameEq : (x, y : UserName) -> Maybe (x = y)
userNameEq (Basic x) (Basic y) with (decEq x y)
  userNameEq (Basic x) (Basic y) | Yes prf = Just (cong Basic prf)
  userNameEq (Basic x) (Basic y) | No nprf = Nothing
userNameEq (Field x) (Field y) with (decEq x y)
  userNameEq (Field x) (Field y) | Yes prf = Just (cong Field prf)
  userNameEq (Field x) (Field y) | No nprf = Nothing
userNameEq Underscore Underscore = Just Refl
userNameEq _ _ = Nothing


export
nameEq : (x : Name) -> (y : Name) -> Maybe (x = y)
nameEq (NS xs x) (NS ys y) with (decEq xs ys)
  nameEq (NS ys x) (NS ys y) | (Yes Refl) with (nameEq x y)
    nameEq (NS ys x) (NS ys y) | (Yes Refl) | Nothing = Nothing
    nameEq (NS ys y) (NS ys y) | (Yes Refl) | (Just Refl) = Just Refl
  nameEq (NS xs x) (NS ys y) | (No contra) = Nothing
nameEq (UN x) (UN y) = map (cong UN) (userNameEq x y)
nameEq (MN x t) (MN x' t') with (decEq x x')
  nameEq (MN x t) (MN x t') | (Yes Refl) with (decEq t t')
    nameEq (MN x t) (MN x t) | (Yes Refl) | (Yes Refl) = Just Refl
    nameEq (MN x t) (MN x t') | (Yes Refl) | (No contra) = Nothing
  nameEq (MN x t) (MN x' t') | (No contra) = Nothing
nameEq (PV x t) (PV y t') with (nameEq x y)
  nameEq (PV y t) (PV y t') | (Just Refl) with (decEq t t')
    nameEq (PV y t) (PV y t) | (Just Refl) | (Yes Refl) = Just Refl
    nameEq (PV y t) (PV y t') | (Just Refl) | (No p) = Nothing
  nameEq (PV x t) (PV y t') | Nothing = Nothing
nameEq (DN x t) (DN y t') with (decEq x y)
  nameEq (DN y t) (DN y t') | (Yes Refl) with (nameEq t t')
    nameEq (DN y t) (DN y t) | (Yes Refl) | (Just Refl) = Just Refl
    nameEq (DN y t) (DN y t') | (Yes Refl) | Nothing = Nothing
  nameEq (DN x t) (DN y t') | (No p) = Nothing
nameEq (WithBlock x y) (WithBlock x' y') with (decEq x x')
  nameEq (WithBlock x y) (WithBlock x' y') | (No p) = Nothing
  nameEq (WithBlock x y) (WithBlock x y') | (Yes Refl) with (decEq y y')
    nameEq (WithBlock x y) (WithBlock x y') | (Yes Refl) | (No p) = Nothing
    nameEq (WithBlock x y) (WithBlock x y) | (Yes Refl) | (Yes Refl) = Just Refl
nameEq (Resolved x) (Resolved y) with (decEq x y)
  nameEq (Resolved y) (Resolved y) | (Yes Refl) = Just Refl
  nameEq (Resolved x) (Resolved y) | (No contra) = Nothing
nameEq _ _ = Nothing

export
namesEq : (xs : List Name) -> (ys : List Name) -> Maybe (xs = ys)
namesEq [] [] = Just Refl
namesEq (x :: xs) (y :: ys)
    = do p <- nameEq x y
         ps <- namesEq xs ys
         rewrite p
         rewrite ps
         Just Refl
namesEq _ _ = Nothing
