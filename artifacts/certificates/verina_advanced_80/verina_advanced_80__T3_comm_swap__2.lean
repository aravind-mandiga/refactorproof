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
          findIndices i (1 + j) fuel -- Try next j

  findIndices 0 1 (nums.size * nums.size)
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (nums : Array Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) :
    RPOrig.twoSum nums target h_precond = RPRef.twoSum nums target h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (nums : Array Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) :
    RPOrig.twoSum nums target h_precond = RPRef.twoSum nums target h_precond := rfl

theorem rp_equiv_delta_rfl (nums : Array Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) :
    RPOrig.twoSum nums target h_precond = RPRef.twoSum nums target h_precond := by
  delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.findIndices RPRef.twoSum.findIndices
  rfl

theorem rp_equiv_simp_only (nums : Array Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) :
    RPOrig.twoSum nums target h_precond = RPRef.twoSum nums target h_precond := by
  first
    | (simp only [RPOrig.twoSum, RPRef.twoSum, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.findIndices RPRef.twoSum.findIndices; rfl))
    | (simp only [RPOrig.twoSum, RPRef.twoSum, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.findIndices RPRef.twoSum.findIndices; rfl))
    | (simp only [RPOrig.twoSum, RPRef.twoSum, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.findIndices RPRef.twoSum.findIndices; rfl))
    | (simp only [RPOrig.twoSum, RPRef.twoSum]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.findIndices RPRef.twoSum.findIndices; rfl))

theorem rp_equiv_simp (nums : Array Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) :
    RPOrig.twoSum nums target h_precond = RPRef.twoSum nums target h_precond := by
  first
    | (simp [RPOrig.twoSum, RPRef.twoSum, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.findIndices RPRef.twoSum.findIndices; rfl))
    | (simp [RPOrig.twoSum, RPRef.twoSum, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.findIndices RPRef.twoSum.findIndices; rfl))
    | (simp [RPOrig.twoSum, RPRef.twoSum, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.findIndices RPRef.twoSum.findIndices; rfl))
    | (simp [RPOrig.twoSum, RPRef.twoSum]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.findIndices RPRef.twoSum.findIndices; rfl))

theorem rp_equiv_ac_rfl (nums : Array Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) :
    RPOrig.twoSum nums target h_precond = RPRef.twoSum nums target h_precond := by
  (try simp only [RPOrig.twoSum, RPRef.twoSum]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.findIndices RPRef.twoSum.findIndices; rfl))
