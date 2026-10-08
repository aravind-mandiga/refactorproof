-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def twoSum_precond (nums : Array Int) (target : Int) : Prop :=
  -- !benchmark @start precond
  -- The array must have at least 2 elements
  nums.size ≥ 2 ∧

  -- There exists exactly one pair of indices whose values sum to the target
  (List.range nums.size).any (fun i =>
    (List.range i).any (fun j => nums[i]! + nums[j]! = target)) ∧

  -- No other pair sums to the target (ensuring uniqueness of solution)
  ((List.range nums.size).flatMap (fun i =>
    (List.range i).filter (fun j => nums[i]! + nums[j]! = target))).length = 1
  -- !benchmark @end precond



namespace RPOrig

def twoSum (nums : Array Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) : Array Nat :=
  let rec findIndices (i : Nat) (j : Nat) (fuel : Nat) : Array Nat :=
    match fuel with
    | 0 => #[] -- Fuel exhausted, return empty array
    | fuel+1 =>
      if i >= nums.size then
        #[] -- No solution found
      else if j >= nums.size then
        findIndices (i + 1) (i + 2) fuel -- Move to next i and reset j
      else
        if nums[i]! + nums[j]! == target then
          #[i, j] -- Found solution
        else
          findIndices i (j + 1) fuel -- Try next j

  findIndices 0 1 (nums.size * nums.size)
end RPOrig

namespace RPRef
private def twoSum__rp_helper_9c17cc11 (nums : Array Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) : Array Nat :=
  let rec findIndices (i : Nat) (j : Nat) (fuel : Nat) : Array Nat :=
    match fuel with
    | 0 => #[] -- Fuel exhausted, return empty array
    | fuel+1 =>
      if i >= nums.size then
        #[] -- No solution found
      else if j >= nums.size then
        findIndices (i + 1) (i + 2) fuel -- Move to next i and reset j
      else
        if nums[i]! + nums[j]! == target then
          #[i, j] -- Found solution
        else
          findIndices i (j + 1) fuel -- Try next j

  findIndices 0 1 (nums.size * nums.size)

def twoSum (nums : Array Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) : Array Nat :=
  twoSum__rp_helper_9c17cc11 nums target h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (nums : Array Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) :
    RPOrig.twoSum nums target h_precond = RPRef.twoSum nums target h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (nums : Array Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) :
    RPOrig.twoSum nums target h_precond = RPRef.twoSum nums target h_precond := rfl

theorem rp_equiv_delta_rfl (nums : Array Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) :
    RPOrig.twoSum nums target h_precond = RPRef.twoSum nums target h_precond := by
  delta RPOrig.twoSum RPRef.twoSum RPRef.twoSum__rp_helper_9c17cc11 RPOrig.twoSum.findIndices RPRef.twoSum__rp_helper_9c17cc11.findIndices
  rfl

theorem rp_equiv_simp_only (nums : Array Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) :
    RPOrig.twoSum nums target h_precond = RPRef.twoSum nums target h_precond := by
  (simp only [RPOrig.twoSum, RPRef.twoSum, RPRef.twoSum__rp_helper_9c17cc11]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.twoSum RPRef.twoSum RPRef.twoSum__rp_helper_9c17cc11 RPOrig.twoSum.findIndices RPRef.twoSum__rp_helper_9c17cc11.findIndices; rfl))

theorem rp_equiv_simp (nums : Array Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) :
    RPOrig.twoSum nums target h_precond = RPRef.twoSum nums target h_precond := by
  (simp [RPOrig.twoSum, RPRef.twoSum, RPRef.twoSum__rp_helper_9c17cc11]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.twoSum RPRef.twoSum RPRef.twoSum__rp_helper_9c17cc11 RPOrig.twoSum.findIndices RPRef.twoSum__rp_helper_9c17cc11.findIndices; rfl))
