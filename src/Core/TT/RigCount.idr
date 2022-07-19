module Core.TT.RigCount

public export
data RigCount = Rig0 | Rig1 | RigW

export
rigPlus : RigCount -> RigCount -> RigCount
rigPlus Rig0 a = a
rigPlus a Rig0 = a
rigPlus _ _ = RigW

export
rigMult : RigCount -> RigCount -> RigCount
rigMult Rig0 _ = Rig0
rigMult _ Rig0 = Rig0
rigMult Rig1 a = a
rigMult a Rig1 = a
rigMult _ _ = RigW

export
rigDivW : RigCount -> RigCount
rigDivW Rig1 = Rig0
rigDivW a = a

-- rigDiv a b is largest c s.t c * b <= a
export
rigDiv : RigCount -> RigCount -> RigCount
rigDiv a Rig0 = RigW
rigDiv a Rig1 = a
rigDiv a RigW = rigDivW a

export
Show RigCount where
  show Rig0 = "0"
  show Rig1 = "1"
  show RigW = ""

export
Eq RigCount where
  Rig0 == Rig0 = True
  Rig1 == Rig1 = True
  RigW == RigW = True
  _ == _ = False

export
Ord RigCount where
  compare x y = compare (tag x) (tag y)
    where
      tag : RigCount -> Int
      tag Rig0 = 0
      tag Rig1 = 1
      tag RigW = 2

export
erased : RigCount
erased = Rig0

export
linear : RigCount
linear = Rig1

export
top : RigCount
top = RigW

export
isErased : RigCount -> Bool
isErased Rig0 = True
isErased _ = False

export
isLinear : RigCount -> Bool
isLinear Rig1 = True
isLinear _ = False

export
isRigOther : RigCount -> Bool
isRigOther RigW = True
isRigOther _ = False

||| A semiring eliminator
public export
elimSemi : (zero : b) -> (one : b) -> (RigCount -> b) -> RigCount -> b
elimSemi zero one other Rig0 = zero
elimSemi zero one other Rig1 = one
elimSemi zero one other RigW = other RigW

export
branchZero : Lazy b -> Lazy b -> RigCount -> b
branchZero yes no rig = if isErased rig then yes else no

export
branchOne : Lazy b -> Lazy b -> RigCount -> b
branchOne yes no rig = if isLinear rig then yes else no

export
branchVal : Lazy b -> Lazy b -> RigCount -> b
branchVal yes no rig = if isRigOther rig then yes else no

export
relevance : RigCount -> RigCount
relevance Rig0 = Rig0
relevance _ = Rig1
