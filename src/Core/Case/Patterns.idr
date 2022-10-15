module Core.Case.Patterns

import Core.Context
import Core.TT

import Data.List
import Data.SnocList
import Data.String

import Libraries.Data.NameMap
import Libraries.Text.PrettyPrint.Prettyprinter
import Libraries.Data.String.Extra

public export
data Pat : Type where
     PAs : FC -> Name -> Pat -> Pat
     PCon : FC -> Name -> (tag : Int) -> (arity : Nat) ->
            SnocList (RigCount, Pat) -> Pat
     PTyCon : FC -> Name -> (arity : Nat) -> SnocList (RigCount, Pat) -> Pat
     PConst : FC -> (c : Constant) -> Pat
     PArrow : FC -> (x : Name) -> Pat -> Pat -> Pat
     PDelay : FC -> LazyReason -> Pat -> Pat -> Pat
     -- TODO: Matching on lazy types
     PLoc : FC -> Name -> Pat
     PUnmatchable : FC -> ClosedTerm -> Pat

export
isPConst : Pat -> Maybe Constant
isPConst (PConst _ c) = Just c
isPConst _ = Nothing

export
covering
Show Pat where
  show (PAs _ n p) = show n ++ "@(" ++ show p ++ ")"
  show (PCon _ n i _ args)
      = show n ++ " " ++ show i ++ " " ++ assert_total (show (map snd args))
  show (PTyCon _ n _ args)
      = "<TyCon>" ++ show n ++ " " ++ assert_total (show (map snd args))
  show (PConst _ c) = show c
  show (PArrow _ x s t) = "(" ++ show s ++ " -> " ++ show t ++ ")"
  show (PDelay _ _ _ p) = "(Delay " ++ show p ++ ")"
  show (PLoc _ n) = show n
  show (PUnmatchable _ tm) = ".(" ++ show tm ++ ")"

export
HasNames Pat where
  full gam (PAs fc n p)
     = [| PAs (pure fc) (full gam n) (full gam p) |]
  full gam (PCon fc n i ar ps)
     = [| PCon (pure fc) (full gam n) (pure i) (pure ar) (traverseSnocList (full gam) ps) |]
  full gam (PTyCon fc n ar ps)
     = [| PTyCon (pure fc) (full gam n) (pure ar) (traverseSnocList (full gam) ps) |]
  full gam p@(PConst _ _) = pure p
  full gam (PArrow fc x p q)
     = [| PArrow (pure fc) (full gam x) (full gam p) (full gam q) |]
  full gam (PDelay fc laz p q)
     = [| PDelay (pure fc) (pure laz) (full gam p) (full gam q) |]
  full gam (PLoc fc n) = PLoc fc <$> full gam n
  full gam (PUnmatchable fc t) = PUnmatchable fc <$> full gam t

  resolved gam (PAs fc n p)
     = [| PAs (pure fc) (resolved gam n) (resolved gam p) |]
  resolved gam (PCon fc n i ar ps)
     = [| PCon (pure fc) (resolved gam n) (pure i) (pure ar) (traverseSnocList (resolved gam) ps) |]
  resolved gam (PTyCon fc n ar ps)
     = [| PTyCon (pure fc) (resolved gam n) (pure ar) (traverseSnocList (resolved gam) ps) |]
  resolved gam p@(PConst _ _) = pure p
  resolved gam (PArrow fc x p q)
     = [| PArrow (pure fc) (resolved gam x) (resolved gam p) (resolved gam q) |]
  resolved gam (PDelay fc laz p q)
     = [| PDelay (pure fc) (pure laz) (resolved gam p) (resolved gam q) |]
  resolved gam (PLoc fc n) = PLoc fc <$> resolved gam n
  resolved gam (PUnmatchable fc t) = PUnmatchable fc <$> resolved gam t

export
mkTerm : (vars : SnocList Name) -> Pat -> Term vars
mkTerm vars (PAs fc x y) = mkTerm vars y
mkTerm vars (PCon fc x tag arity xs)
    = applySpine fc (Ref fc (DataCon tag arity) x)
               (map (\ (c, t) => (c, mkTerm vars t)) xs)
mkTerm vars (PTyCon fc x arity xs)
    = applySpine fc (Ref fc (TyCon arity) x)
               (map (\ (c, t) => (c, mkTerm vars t)) xs)
mkTerm vars (PConst fc c) = PrimVal fc c
mkTerm vars (PArrow fc x s t)
    = Bind fc x (Pi fc top Explicit (mkTerm vars s)) (mkTerm (vars :< x) t)
mkTerm vars (PDelay fc r ty p)
    = TDelay fc r (mkTerm vars ty) (mkTerm vars p)
mkTerm vars (PLoc fc n)
    = case isVar n vars of
           Just (MkVar prf) => Local fc Nothing _ prf
           _ => Ref fc Bound n
mkTerm vars (PUnmatchable fc tm) = embed tm
