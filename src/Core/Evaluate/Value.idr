module Core.Evaluate.Value

import Core.Core
import Core.Error
import Core.TT

import Data.SnocList
import Data.Vect

public export
data Form = Glue | Normal

public export
data Value : Form -> SnocList Name -> Type

public export
Glued : SnocList Name -> Type
Glued = Value Glue

public export
NF : SnocList Name -> Type
NF = Value Normal

public export
data VCaseAlt : SnocList Name -> Type

public export
0 Spine : SnocList Name -> Type
Spine vars = SnocList (FC, RigCount, Glued vars)

-- The 'Form' is a phantom type index that says whether we know the value is
-- in normal form, or whether it might be 'Glued'
-- In theory, we know that everything except 'VApp' and "VMeta' are Normal,
-- but in practice this is annoying because evaluating doesn't know whether
-- it's going to produce a 'Glued' or a 'Normal'.
-- The phantom index gives us enough help, specifically in that it means we
-- are sure that we've expanded to head normal Normal form before processing
-- a Value
public export
data Value : Form -> SnocList Name -> Type where
     -- Lambdas - we also have a value for binders in general, but
     -- lambdas are the most common, so save the pattern match/indirection
     VLam : FC -> (x : Name) -> RigCount -> PiInfo (Glued vars) ->
            (ty : Glued vars) ->
            (sc : Glued vars -> Core (Glued vars)) ->
            Value f vars
     VBind : FC -> (x : Name) -> Binder (Glued vars) ->
             (sc : Glued vars -> Core (Glued vars)) ->
             Value f vars
     -- A 'glued' application. This includes the original application
     -- (for quoting back HNFs) and what it reduces to (if the name is
     -- defined).
     VApp : FC ->
            NameType -> Name -> Spine vars -> -- original form
            Core (Maybe (Glued vars)) -> -- the normal form
            Value f vars
     VLocal   : FC -> Maybe Bool -> (idx : Nat) -> (0 p : IsVar n idx vars) ->
                Spine vars ->
                Value f vars
     VMeta  : FC -> Name -> Int -> -- Name and resolved name of metavar
              List (RigCount, Glued vars) -> -- Scope of metavar
              Spine vars ->
              Core (Maybe (Glued vars)) -> -- the normal form, if solved
              Value f vars
     VDCon    : FC -> Name -> (tag : Tag) -> (arity : Nat) ->
                Spine vars -> Value f vars
     VTCon    : FC -> Name -> (arity : Nat) ->
                Spine vars -> Value f vars
     VAs      : FC -> UseSide -> Value f vars -> Value f vars -> Value f vars
     VCase    : FC -> RigCount -> (sc : Glued vars) -> (scTy : Glued vars) ->
                List (VCaseAlt vars) ->
                Value f vars
     VDelayed : FC -> LazyReason -> Glued vars -> Value f vars
     VDelay   : FC -> LazyReason -> Glued vars -> Glued vars -> Value f vars
     VForce   : FC -> LazyReason -> Glued vars -> Spine vars -> Value f vars
     VPrimVal : FC -> Constant -> Value f vars
     VPrimOp  : FC -> PrimFn ar -> Vect ar (Glued vars) -> Value f vars
     VErased  : FC -> (imp : Bool) -> Value f vars
     VUnmatched : FC -> String -> Value f vars
     VImpossible : FC -> Value f vars
     VType    : FC -> Name -> Value f vars

export
getLoc : Value f vars -> FC
getLoc (VLam fc x y z ty sc) = fc
getLoc (VBind fc x y sc) = fc
getLoc (VApp fc x y sx z) = fc
getLoc (VLocal fc x idx p sx) = fc
getLoc (VMeta fc x y xs sx z) = fc
getLoc (VDCon fc x tag arity sx) = fc
getLoc (VTCon fc x arity sx) = fc
getLoc (VAs fc x y z) = fc
getLoc (VCase fc x sc scTy xs) = fc
getLoc (VDelayed fc x y) = fc
getLoc (VDelay fc x y z) = fc
getLoc (VForce fc x y sx) = fc
getLoc (VPrimVal fc x) = fc
getLoc (VPrimOp fc x xs) = fc
getLoc (VErased fc imp) = fc
getLoc (VUnmatched fc x) = fc
getLoc (VImpossible fc) = fc
getLoc (VType fc x) = fc

-- If a value is an App or Meta node, then it might be reducible. Expand it
-- just enough that we have the right top level node.
-- The 'believe_me' are there to save us deconstructing and reconstructing
-- just to change a compile-time only index
export
expand : Value f vars -> Core (NF vars)
expand v@(VApp fc nt n sp val)
    = do Just val' <- val
              | Nothing => pure (believe_me v)
         expand val'
expand v@(VMeta fc n i args sp val)
    = do Just val' <- val
              | Nothing => pure (believe_me v)
         expand val'
expand val = pure (believe_me val)

-- It's safe to pretend an NF is Glued, if we need it
export
asGlued : Value f vars -> Glued vars
asGlued = believe_me -- justification as above

export
spineVal : (FC, RigCount, Glued vars) -> Core (NF vars)
spineVal (_, _, val) = expand val

public export
0 VCaseScope : SnocList (RigCount, Name) -> SnocList Name -> Type
VCaseScope [<] vars = Core (Glued vars)
VCaseScope (xs :< x) vars = Glued vars -> VCaseScope xs vars

public export
data VCaseAlt : SnocList Name -> Type where
     ||| Constructor for a data type; bind the arguments and subterms.
     VConCase : FC -> Name -> (tag : Int) ->
                (args : SnocList (RigCount, Name)) ->
                VCaseScope args vars -> VCaseAlt vars
     ||| Lazy match for the Delay type use for codata types
     VDelayCase : FC -> (ty : Name) -> (arg : Name) ->
                  VCaseScope [<(RigCount.top, arg), (RigCount.erased, ty)] vars -> VCaseAlt vars
     ||| Match against a literal
     VConstCase : FC -> Constant -> Glued vars -> VCaseAlt vars
     ||| Catch-all case
     VDefaultCase : FC -> Glued vars -> VCaseAlt vars

-- Show what form a value has, for debugging
export
qshow : Value f vars -> String
qshow (VLam{}) = "Lam"
qshow (VBind{}) = "Bind"
qshow (VApp _ _ n _ _) = "App " ++ show n
qshow (VLocal{}) = "Local"
qshow (VMeta _ n _ _ _ _) = "Meta " ++ show n
qshow (VDCon _ n _ _ _) = "DCon " ++ show n
qshow (VTCon _ n _ _) = "TCon " ++ show n
qshow (VCase{}) = "Case"
qshow (VPrimVal _ c) = "Constant " ++ show c
qshow (VPrimOp _ f args) = "PrimOp " ++ show f ++ " " ++ show (length args)
qshow _ = "???"
