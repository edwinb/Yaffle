module Core.Case.Tree

-- Intermediate form of Case Trees, built by the case tree builder before
-- being turned into a Term
-- The intermediate for allows some checking, especially for unreacable
-- cases

import Core.Context
import Core.TT

import Data.List
import Data.SnocList

public export
data TCaseAlt : SnocList Name -> Type

||| Case trees in A-normal forms
||| i.e. we may only dispatch on variables, not expressions
public export
data CaseTree : SnocList Name -> Type where
     ||| case x return scTy of { p1 => e1 ; ... }
     TCase : {name : _} ->
             FC -> RigCount ->
             (idx : Nat) ->
             (0 p : IsVar name idx vars) ->
             (scTy : Term vars) -> List (TCaseAlt vars) ->
             CaseTree vars
     ||| RHS: no need for further inspection
     ||| The Int is a clause id that allows us to see which of the
     ||| initial clauses are reached in the tree
     ||| Also record forced patterns (i.e. what we know variables are equal
     ||| to based on other matches)
     STerm : Int -> List (Var vars, Term vars) ->
             Term vars -> CaseTree vars
     ||| error from a partial match
     TUnmatched : FC -> (msg : String) -> CaseTree vars
     ||| Absurd context
     TImpossible : FC -> CaseTree vars

public export
data TCaseScope : SnocList Name -> Type where
     TRHS : CaseTree vars -> TCaseScope vars
     TArg : RigCount -> (x : Name) -> TCaseScope (vars :< x) -> TCaseScope vars

||| Case alternatives. Unlike arbitrary patterns, they can be at most
||| one constructor deep.
public export
data TCaseAlt : SnocList Name -> Type where
     ||| Constructor for a data type; bind the arguments and subterms.
     TConCase : FC -> Name -> (tag : Int) -> TCaseScope vars -> TCaseAlt vars
     ||| Lazy match for the Delay type use for codata typesT
     TDelayCase : FC -> (ty : Name) -> (arg : Name) ->
                 CaseTree (vars :< ty :< arg) -> TCaseAlt vars
     ||| Match against a literal
     TConstCase : FC -> Constant -> CaseTree vars -> TCaseAlt vars
     ||| Catch-all case
     TDefaultCase : FC -> CaseTree vars -> TCaseAlt vars

insertCaseAltNames : SizeOf outer ->
                     SizeOf ns ->
                     TCaseAlt (inner ++ outer) ->
                     TCaseAlt (inner ++ ns ++ outer)

insertCaseNames : SizeOf outer ->
                  SizeOf ns ->
                  CaseTree (inner ++ outer) ->
                  CaseTree (inner ++ ns ++ outer)
insertCaseNames outer ns (TCase fc c idx prf scTy alts)
    = let MkNVar prf' = insertNVarNames outer ns (MkNVar prf) in
          TCase fc c _ prf' (insertNames outer ns scTy)
              (map (insertCaseAltNames outer ns) alts)
insertCaseNames outer ns (STerm i vs x)
    = STerm i (map ( \(v, t) => (insertVarNames outer ns v,
                                 insertNames outer ns t)) vs)
              (insertNames outer ns x)
insertCaseNames _ _ (TUnmatched fc msg) = TUnmatched fc msg
insertCaseNames _ _ (TImpossible fc) = TImpossible fc

insertCaseScopeNames : SizeOf outer ->
                       SizeOf ns ->
                       TCaseScope (inner ++ outer) ->
                       TCaseScope (inner ++ ns ++ outer)
insertCaseScopeNames outer ns (TRHS tm) = TRHS (insertCaseNames outer ns tm)
insertCaseScopeNames outer ns (TArg c x sc)
    = TArg c x (insertCaseScopeNames (suc outer) ns sc)

insertCaseAltNames outer ns (TConCase fc n t sc)
    = TConCase fc n t (insertCaseScopeNames outer ns sc)
insertCaseAltNames outer ns (TDelayCase fc ty arg tm)
    = TDelayCase fc ty arg (insertCaseNames (suc (suc outer)) ns tm)
insertCaseAltNames outer ns (TConstCase fc c sc)
    = TConstCase fc c (insertCaseNames outer ns sc)
insertCaseAltNames outer ns (TDefaultCase fc sc)
    = TDefaultCase fc (insertCaseNames outer ns sc)


export
Weaken CaseTree where
  weakenNs ns t = insertCaseNames zero ns t

export
Weaken TCaseScope where
  weakenNs ns t = insertCaseScopeNames zero ns t

export
mkCaseAlt : CaseType -> TCaseAlt vars -> CaseAlt vars

export
mkTerm : CaseType -> CaseTree vars -> Term vars
mkTerm ct (TCase fc c idx p scTy xs)
   = Case fc ct c (Local fc idx p) scTy (map (mkCaseAlt ct) xs)
-- If there's forced equalities, we processed them in 'TRHS'. They shouldn't
-- appear outside a case branch, so ignore them here.
mkTerm _ (STerm i _ tm) = tm
mkTerm _ (TUnmatched fc msg) = Unmatched fc msg
mkTerm _ (TImpossible fc) = Erased fc Impossible

mkCaseScope : CaseType -> TCaseScope vars -> CaseScope vars
mkCaseScope ct (TRHS (STerm _ fs tm)) = RHS fs tm
mkCaseScope ct (TRHS tm) = RHS [] (mkTerm ct tm)
mkCaseScope ct (TArg c x sc) = Arg c x (mkCaseScope ct sc)

mkCaseAlt ct (TConCase fc x tag sc) = ConCase fc x tag (mkCaseScope ct sc)
mkCaseAlt ct (TDelayCase fc ty arg tm) = DelayCase fc ty arg (mkTerm ct tm)
mkCaseAlt ct (TConstCase fc c tm) = ConstCase fc c (mkTerm ct tm)
mkCaseAlt ct (TDefaultCase fc tm) = DefaultCase fc (mkTerm ct tm)

showCT : {vars : _} -> (indent : String) -> CaseTree vars -> String
showCA : {vars : _} -> (indent : String) -> TCaseAlt vars  -> String

showCT indent (TCase {name} fc c idx prf ty alts)
  = "case " ++ show name ++ "[" ++ show idx ++ "] : " ++ show ty ++ " of"
  ++ "\n" ++ indent ++ " { "
  ++ showSep ("\n" ++ indent ++ " | ")
             (assert_total (map (showCA ("  " ++ indent)) alts))
  ++ "\n" ++ indent ++ " }"
showCT indent (STerm i vs tm)
   = "[" ++ show i ++ ": " ++ showSep "," (map showForced vs) ++ "] " ++ show tm
  where
    showForced : (Var vars, Term vars) -> String
    showForced (MkVar v, tm) = show (Local EmptyFC _ v) ++ " = " ++ show tm
showCT indent (TUnmatched fc msg) = "Error: " ++ show msg
showCT indent (TImpossible fc) = "Impossible"

showCA indent (TConCase fc n tag sc)
        = show n ++ " " ++ showScope sc
  where
    showScope : {vars : _} -> TCaseScope vars -> String
    showScope (TRHS tm) = " => " ++ showCT indent tm
    showScope (TArg c x sc) = show x ++ " " ++ showScope sc
showCA indent (TDelayCase _ _ arg sc)
        = "Delay " ++ show arg ++ " => " ++ showCT indent sc
showCA indent (TConstCase _ c sc)
        = "Constant " ++ show c ++ " => " ++ showCT indent sc
showCA indent (TDefaultCase _ sc)
        = "_ => " ++ showCT indent sc

export
covering
{vars : _} -> Show (CaseTree vars) where
  show = showCT ""

export
covering
{vars : _} -> Show (TCaseAlt vars) where
  show = showCA ""
