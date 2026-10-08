-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def rain_precond (heights : List (Int)) : Prop :=
  -- !benchmark @start precond
  heights.all (fun h => h >= 0)
  -- !benchmark @end precond



namespace RPOrig

def rain (heights : List (Int)) (h_precond : rain_precond (heights)) : Int :=
  -- Handle edge cases: need at least 3 elements to trap water
  if heights.length < 3 then 0 else
    let n := heights.length

    -- Use two pointers approach for O(n) time with O(1) space
    let rec aux (left : Nat) (right : Nat) (leftMax : Int) (rightMax : Int) (water : Int) : Int :=
      if left >= right then
        water  -- Base case: all elements processed
      else if heights[left]! <= heights[right]! then
        -- Process from the left
        let newLeftMax := max leftMax (heights[left]!)
        let newWater := water + max 0 (leftMax - heights[left]!)
        aux (left+1) right newLeftMax rightMax newWater
      else
        -- Process from the right
        let newRightMax := max rightMax (heights[right]!)
        let newWater := water + max 0 (rightMax - heights[right]!)
        aux left (right-1) leftMax newRightMax newWater
      termination_by right - left
    -- Initialize with two pointers at the ends
    aux 0 (n-1) (heights[0]!) (heights[n-1]!) 0
end RPOrig

namespace RPRef
private def rain__rp_helper_347f6434 (heights : List (Int)) (h_precond : rain_precond (heights)) : Int :=
  -- Handle edge cases: need at least 3 elements to trap water
  if heights.length < 3 then 0 else
    let n := heights.length

    -- Use two pointers approach for O(n) time with O(1) space
    let rec aux (left : Nat) (right : Nat) (leftMax : Int) (rightMax : Int) (water : Int) : Int :=
      if left >= right then
        water  -- Base case: all elements processed
      else if heights[left]! <= heights[right]! then
        -- Process from the left
        let newLeftMax := max leftMax (heights[left]!)
        let newWater := water + max 0 (leftMax - heights[left]!)
        aux (left+1) right newLeftMax rightMax newWater
      else
        -- Process from the right
        let newRightMax := max rightMax (heights[right]!)
        let newWater := water + max 0 (rightMax - heights[right]!)
        aux left (right-1) leftMax newRightMax newWater
      termination_by right - left
    -- Initialize with two pointers at the ends
    aux 0 (n-1) (heights[0]!) (heights[n-1]!) 0

def rain (heights : List (Int)) (h_precond : rain_precond (heights)) : Int :=
  rain__rp_helper_347f6434 heights h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (heights : List (Int)) (h_precond : rain_precond (heights)) :
    RPOrig.rain heights h_precond = RPRef.rain heights h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (heights : List (Int)) (h_precond : rain_precond (heights)) :
    RPOrig.rain heights h_precond = RPRef.rain heights h_precond := rfl

theorem rp_equiv_delta_rfl (heights : List (Int)) (h_precond : rain_precond (heights)) :
    RPOrig.rain heights h_precond = RPRef.rain heights h_precond := by
  delta RPOrig.rain RPRef.rain RPRef.rain__rp_helper_347f6434 RPOrig.rain.aux RPRef.rain__rp_helper_347f6434.aux
  rfl

theorem rp_equiv_simp_only (heights : List (Int)) (h_precond : rain_precond (heights)) :
    RPOrig.rain heights h_precond = RPRef.rain heights h_precond := by
  (simp only [RPOrig.rain, RPRef.rain, RPRef.rain__rp_helper_347f6434]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.rain RPRef.rain RPRef.rain__rp_helper_347f6434 RPOrig.rain.aux RPRef.rain__rp_helper_347f6434.aux; rfl))

theorem rp_equiv_simp (heights : List (Int)) (h_precond : rain_precond (heights)) :
    RPOrig.rain heights h_precond = RPRef.rain heights h_precond := by
  (simp [RPOrig.rain, RPRef.rain, RPRef.rain__rp_helper_347f6434]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.rain RPRef.rain RPRef.rain__rp_helper_347f6434 RPOrig.rain.aux RPRef.rain__rp_helper_347f6434.aux; rfl))
