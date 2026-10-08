-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def trapRainWater_precond (height : List Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def trapLoop (height : List Nat) (left right leftMax rightMax water : Nat) : Nat :=
  if h : left < right then
    let hLeft := height[left]!
    let hRight := height[right]!
    if hLeft < hRight then
      let (leftMax, water) :=
        if hLeft >= leftMax then (hLeft, water) else (leftMax, water + (leftMax - hLeft))
      trapLoop height (left + 1) right leftMax rightMax water
    else
      let (rightMax, water) :=
        if hRight >= rightMax then (hRight, water) else (rightMax, water + (rightMax - hRight))
      trapLoop height left (right - 1) leftMax rightMax water
  else
    water
termination_by right - left

namespace RPOrig

def trapRainWater (height : List Nat) (h_precond : trapRainWater_precond (height)) : Nat :=
  trapLoop height 0 (height.length - 1) 0 0 0
end RPOrig

namespace RPRef

private def trapRainWater__rp_helper_bad67bda (height : List Nat) (h_precond : trapRainWater_precond (height)) : Nat :=
  trapLoop height 0 (height.length - 1) 0 0 0

def trapRainWater (height : List Nat) (h_precond : trapRainWater_precond (height)) : Nat :=
  trapRainWater__rp_helper_bad67bda height h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (height : List Nat) (h_precond : trapRainWater_precond (height)) :
    RPOrig.trapRainWater height h_precond = RPRef.trapRainWater height h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (height : List Nat) (h_precond : trapRainWater_precond (height)) :
    RPOrig.trapRainWater height h_precond = RPRef.trapRainWater height h_precond := rfl

theorem rp_equiv_delta_rfl (height : List Nat) (h_precond : trapRainWater_precond (height)) :
    RPOrig.trapRainWater height h_precond = RPRef.trapRainWater height h_precond := by
  delta RPOrig.trapRainWater RPRef.trapRainWater RPRef.trapRainWater__rp_helper_bad67bda
  rfl

theorem rp_equiv_simp_only (height : List Nat) (h_precond : trapRainWater_precond (height)) :
    RPOrig.trapRainWater height h_precond = RPRef.trapRainWater height h_precond := by
  (simp only [RPOrig.trapRainWater, RPRef.trapRainWater, RPRef.trapRainWater__rp_helper_bad67bda]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.trapRainWater RPRef.trapRainWater RPRef.trapRainWater__rp_helper_bad67bda; rfl))

theorem rp_equiv_simp (height : List Nat) (h_precond : trapRainWater_precond (height)) :
    RPOrig.trapRainWater height h_precond = RPRef.trapRainWater height h_precond := by
  (simp [RPOrig.trapRainWater, RPRef.trapRainWater, RPRef.trapRainWater__rp_helper_bad67bda]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.trapRainWater RPRef.trapRainWater RPRef.trapRainWater__rp_helper_bad67bda; rfl))
