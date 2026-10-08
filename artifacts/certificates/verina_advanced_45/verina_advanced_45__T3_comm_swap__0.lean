-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def maxSubarraySum_precond (xs : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def maxSubarraySum (xs : List Int) (h_precond : maxSubarraySum_precond (xs)) : Int :=
  let rec helper (lst : List Int) (curMax : Int) (globalMax : Int) : Int :=
    match lst with
    | [] => globalMax
    | x :: rest =>
      let newCurMax := max x (curMax + x)
      let newGlobal := max globalMax newCurMax
      helper rest newCurMax newGlobal
  match xs with
  | [] => 0
  | x :: rest => helper rest x x
end RPOrig

namespace RPRef

def maxSubarraySum (xs : List Int) (h_precond : maxSubarraySum_precond (xs)) : Int :=
  let rec helper (lst : List Int) (curMax : Int) (globalMax : Int) : Int :=
    match lst with
    | [] => globalMax
    | x :: rest =>
      let newCurMax := max x (x + curMax)
      let newGlobal := max globalMax newCurMax
      helper rest newCurMax newGlobal
  match xs with
  | [] => 0
  | x :: rest => helper rest x x
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (xs : List Int) (h_precond : maxSubarraySum_precond (xs)) :
    RPOrig.maxSubarraySum xs h_precond = RPRef.maxSubarraySum xs h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (xs : List Int) (h_precond : maxSubarraySum_precond (xs)) :
    RPOrig.maxSubarraySum xs h_precond = RPRef.maxSubarraySum xs h_precond := rfl

theorem rp_equiv_delta_rfl (xs : List Int) (h_precond : maxSubarraySum_precond (xs)) :
    RPOrig.maxSubarraySum xs h_precond = RPRef.maxSubarraySum xs h_precond := by
  delta RPOrig.maxSubarraySum RPRef.maxSubarraySum RPOrig.maxSubarraySum.helper RPRef.maxSubarraySum.helper
  rfl

theorem rp_equiv_simp_only (xs : List Int) (h_precond : maxSubarraySum_precond (xs)) :
    RPOrig.maxSubarraySum xs h_precond = RPRef.maxSubarraySum xs h_precond := by
  first
    | (simp only [RPOrig.maxSubarraySum, RPRef.maxSubarraySum, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxSubarraySum RPRef.maxSubarraySum RPOrig.maxSubarraySum.helper RPRef.maxSubarraySum.helper; rfl))
    | (simp only [RPOrig.maxSubarraySum, RPRef.maxSubarraySum, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxSubarraySum RPRef.maxSubarraySum RPOrig.maxSubarraySum.helper RPRef.maxSubarraySum.helper; rfl))
    | (simp only [RPOrig.maxSubarraySum, RPRef.maxSubarraySum, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxSubarraySum RPRef.maxSubarraySum RPOrig.maxSubarraySum.helper RPRef.maxSubarraySum.helper; rfl))
    | (simp only [RPOrig.maxSubarraySum, RPRef.maxSubarraySum]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxSubarraySum RPRef.maxSubarraySum RPOrig.maxSubarraySum.helper RPRef.maxSubarraySum.helper; rfl))

theorem rp_equiv_simp (xs : List Int) (h_precond : maxSubarraySum_precond (xs)) :
    RPOrig.maxSubarraySum xs h_precond = RPRef.maxSubarraySum xs h_precond := by
  first
    | (simp [RPOrig.maxSubarraySum, RPRef.maxSubarraySum, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxSubarraySum RPRef.maxSubarraySum RPOrig.maxSubarraySum.helper RPRef.maxSubarraySum.helper; rfl))
    | (simp [RPOrig.maxSubarraySum, RPRef.maxSubarraySum, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxSubarraySum RPRef.maxSubarraySum RPOrig.maxSubarraySum.helper RPRef.maxSubarraySum.helper; rfl))
    | (simp [RPOrig.maxSubarraySum, RPRef.maxSubarraySum, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxSubarraySum RPRef.maxSubarraySum RPOrig.maxSubarraySum.helper RPRef.maxSubarraySum.helper; rfl))
    | (simp [RPOrig.maxSubarraySum, RPRef.maxSubarraySum]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxSubarraySum RPRef.maxSubarraySum RPOrig.maxSubarraySum.helper RPRef.maxSubarraySum.helper; rfl))

theorem rp_equiv_ac_rfl (xs : List Int) (h_precond : maxSubarraySum_precond (xs)) :
    RPOrig.maxSubarraySum xs h_precond = RPRef.maxSubarraySum xs h_precond := by
  (try simp only [RPOrig.maxSubarraySum, RPRef.maxSubarraySum]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxSubarraySum RPRef.maxSubarraySum RPOrig.maxSubarraySum.helper RPRef.maxSubarraySum.helper; rfl))
