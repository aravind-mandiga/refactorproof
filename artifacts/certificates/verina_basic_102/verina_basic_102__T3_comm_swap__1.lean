-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def twoSum_precond (nums : Array Int) (target : Int) : Prop :=
  -- !benchmark @start precond
  nums.size > 1 ∧ ¬ List.Pairwise (fun a b => a + b ≠ target) nums.toList
  -- !benchmark @end precond



namespace RPOrig

def twoSum (nums : Array Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) : (Nat × Nat) :=
  let n := nums.size
  let rec outer (i : Nat) : Option (Nat × Nat) :=
    if i < n - 1 then
      let rec inner (j : Nat) : Option (Nat × Nat) :=
        if j < n then
          if nums[i]! + nums[j]! = target then
            some (i, j)
          else
            inner (j + 1)
        else
          none
      match inner (i + 1) with
      | some pair => some pair
      | none      => outer (i + 1)
    else
      none
  match outer 0 with
  | some pair => pair
  | none      => panic "twoSum: no solution found"
end RPOrig

namespace RPRef

def twoSum (nums : Array Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) : (Nat × Nat) :=
  let n := nums.size
  let rec outer (i : Nat) : Option (Nat × Nat) :=
    if i < n - 1 then
      let rec inner (j : Nat) : Option (Nat × Nat) :=
        if j < n then
          if nums[i]! + nums[j]! = target then
            some (i, j)
          else
            inner (j + 1)
        else
          none
      match inner (1 + i) with
      | some pair => some pair
      | none      => outer (i + 1)
    else
      none
  match outer 0 with
  | some pair => pair
  | none      => panic "twoSum: no solution found"
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (nums : Array Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) :
    RPOrig.twoSum nums target h_precond = RPRef.twoSum nums target h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (nums : Array Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) :
    RPOrig.twoSum nums target h_precond = RPRef.twoSum nums target h_precond := rfl

theorem rp_equiv_delta_rfl (nums : Array Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) :
    RPOrig.twoSum nums target h_precond = RPRef.twoSum nums target h_precond := by
  first
    | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner; rfl)
    | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner RPOrig.twoSum._unary RPOrig.twoSum.outer._unary RPOrig.twoSum.outer.inner._unary RPRef.twoSum.outer._unary RPRef.twoSum.outer.inner._unary; rfl)
    | (set_option smartUnfolding false in rfl)

theorem rp_equiv_simp_only (nums : Array Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) :
    RPOrig.twoSum nums target h_precond = RPRef.twoSum nums target h_precond := by
  first
    | (simp only [RPOrig.twoSum, RPRef.twoSum, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner; rfl) | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner RPOrig.twoSum._unary RPOrig.twoSum.outer._unary RPOrig.twoSum.outer.inner._unary RPRef.twoSum.outer._unary RPRef.twoSum.outer.inner._unary; rfl) | (set_option smartUnfolding false in rfl))
    | (simp only [RPOrig.twoSum, RPRef.twoSum, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner; rfl) | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner RPOrig.twoSum._unary RPOrig.twoSum.outer._unary RPOrig.twoSum.outer.inner._unary RPRef.twoSum.outer._unary RPRef.twoSum.outer.inner._unary; rfl) | (set_option smartUnfolding false in rfl))
    | (simp only [RPOrig.twoSum, RPRef.twoSum, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner; rfl) | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner RPOrig.twoSum._unary RPOrig.twoSum.outer._unary RPOrig.twoSum.outer.inner._unary RPRef.twoSum.outer._unary RPRef.twoSum.outer.inner._unary; rfl) | (set_option smartUnfolding false in rfl))
    | (simp only [RPOrig.twoSum, RPRef.twoSum]) <;> (first | rfl | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner; rfl) | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner RPOrig.twoSum._unary RPOrig.twoSum.outer._unary RPOrig.twoSum.outer.inner._unary RPRef.twoSum.outer._unary RPRef.twoSum.outer.inner._unary; rfl) | (set_option smartUnfolding false in rfl))

theorem rp_equiv_simp (nums : Array Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) :
    RPOrig.twoSum nums target h_precond = RPRef.twoSum nums target h_precond := by
  first
    | (simp [RPOrig.twoSum, RPRef.twoSum, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner; rfl) | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner RPOrig.twoSum._unary RPOrig.twoSum.outer._unary RPOrig.twoSum.outer.inner._unary RPRef.twoSum.outer._unary RPRef.twoSum.outer.inner._unary; rfl) | (set_option smartUnfolding false in rfl))
    | (simp [RPOrig.twoSum, RPRef.twoSum, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner; rfl) | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner RPOrig.twoSum._unary RPOrig.twoSum.outer._unary RPOrig.twoSum.outer.inner._unary RPRef.twoSum.outer._unary RPRef.twoSum.outer.inner._unary; rfl) | (set_option smartUnfolding false in rfl))
    | (simp [RPOrig.twoSum, RPRef.twoSum, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner; rfl) | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner RPOrig.twoSum._unary RPOrig.twoSum.outer._unary RPOrig.twoSum.outer.inner._unary RPRef.twoSum.outer._unary RPRef.twoSum.outer.inner._unary; rfl) | (set_option smartUnfolding false in rfl))
    | (simp [RPOrig.twoSum, RPRef.twoSum]) <;> (first | rfl | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner; rfl) | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner RPOrig.twoSum._unary RPOrig.twoSum.outer._unary RPOrig.twoSum.outer.inner._unary RPRef.twoSum.outer._unary RPRef.twoSum.outer.inner._unary; rfl) | (set_option smartUnfolding false in rfl))

theorem rp_equiv_ac_rfl (nums : Array Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) :
    RPOrig.twoSum nums target h_precond = RPRef.twoSum nums target h_precond := by
  (try simp only [RPOrig.twoSum, RPRef.twoSum]) <;> (try ac_nf) <;> (first | rfl | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner; rfl) | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner RPOrig.twoSum._unary RPOrig.twoSum.outer._unary RPOrig.twoSum.outer.inner._unary RPRef.twoSum.outer._unary RPRef.twoSum.outer.inner._unary; rfl) | (set_option smartUnfolding false in rfl))
