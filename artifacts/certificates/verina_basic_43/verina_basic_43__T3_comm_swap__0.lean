-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def sumOfFourthPowerOfOddNumbers_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def sumOfFourthPowerOfOddNumbers (n : Nat) (h_precond : sumOfFourthPowerOfOddNumbers_precond (n)) : Nat :=
  match n with
  | 0 => 0
  | n + 1 =>
    let prev := sumOfFourthPowerOfOddNumbers n h_precond
    let nextOdd := 2 * n + 1
    prev + nextOdd^4
end RPOrig

namespace RPRef

def sumOfFourthPowerOfOddNumbers (n : Nat) (h_precond : sumOfFourthPowerOfOddNumbers_precond (n)) : Nat :=
  match n with
  | 0 => 0
  | n + 1 =>
    let prev := sumOfFourthPowerOfOddNumbers n h_precond
    let nextOdd := n * 2 + 1
    prev + nextOdd^4
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (n : Nat) (h_precond : sumOfFourthPowerOfOddNumbers_precond (n)) :
    RPOrig.sumOfFourthPowerOfOddNumbers n h_precond = RPRef.sumOfFourthPowerOfOddNumbers n h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (n : Nat) (h_precond : sumOfFourthPowerOfOddNumbers_precond (n)) :
    RPOrig.sumOfFourthPowerOfOddNumbers n h_precond = RPRef.sumOfFourthPowerOfOddNumbers n h_precond := rfl

theorem rp_equiv_delta_rfl (n : Nat) (h_precond : sumOfFourthPowerOfOddNumbers_precond (n)) :
    RPOrig.sumOfFourthPowerOfOddNumbers n h_precond = RPRef.sumOfFourthPowerOfOddNumbers n h_precond := by
  delta RPOrig.sumOfFourthPowerOfOddNumbers RPRef.sumOfFourthPowerOfOddNumbers
  rfl

theorem rp_equiv_simp_only (n : Nat) (h_precond : sumOfFourthPowerOfOddNumbers_precond (n)) :
    RPOrig.sumOfFourthPowerOfOddNumbers n h_precond = RPRef.sumOfFourthPowerOfOddNumbers n h_precond := by
  first
    | (simp only [RPOrig.sumOfFourthPowerOfOddNumbers, RPRef.sumOfFourthPowerOfOddNumbers, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.sumOfFourthPowerOfOddNumbers RPRef.sumOfFourthPowerOfOddNumbers; rfl))
    | (simp only [RPOrig.sumOfFourthPowerOfOddNumbers, RPRef.sumOfFourthPowerOfOddNumbers, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.sumOfFourthPowerOfOddNumbers RPRef.sumOfFourthPowerOfOddNumbers; rfl))
    | (simp only [RPOrig.sumOfFourthPowerOfOddNumbers, RPRef.sumOfFourthPowerOfOddNumbers, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.sumOfFourthPowerOfOddNumbers RPRef.sumOfFourthPowerOfOddNumbers; rfl))
    | (simp only [RPOrig.sumOfFourthPowerOfOddNumbers, RPRef.sumOfFourthPowerOfOddNumbers]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.sumOfFourthPowerOfOddNumbers RPRef.sumOfFourthPowerOfOddNumbers; rfl))

theorem rp_equiv_simp (n : Nat) (h_precond : sumOfFourthPowerOfOddNumbers_precond (n)) :
    RPOrig.sumOfFourthPowerOfOddNumbers n h_precond = RPRef.sumOfFourthPowerOfOddNumbers n h_precond := by
  first
    | (simp [RPOrig.sumOfFourthPowerOfOddNumbers, RPRef.sumOfFourthPowerOfOddNumbers, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.sumOfFourthPowerOfOddNumbers RPRef.sumOfFourthPowerOfOddNumbers; rfl))
    | (simp [RPOrig.sumOfFourthPowerOfOddNumbers, RPRef.sumOfFourthPowerOfOddNumbers, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.sumOfFourthPowerOfOddNumbers RPRef.sumOfFourthPowerOfOddNumbers; rfl))
    | (simp [RPOrig.sumOfFourthPowerOfOddNumbers, RPRef.sumOfFourthPowerOfOddNumbers, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.sumOfFourthPowerOfOddNumbers RPRef.sumOfFourthPowerOfOddNumbers; rfl))
    | (simp [RPOrig.sumOfFourthPowerOfOddNumbers, RPRef.sumOfFourthPowerOfOddNumbers]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.sumOfFourthPowerOfOddNumbers RPRef.sumOfFourthPowerOfOddNumbers; rfl))

theorem rp_equiv_ac_rfl (n : Nat) (h_precond : sumOfFourthPowerOfOddNumbers_precond (n)) :
    RPOrig.sumOfFourthPowerOfOddNumbers n h_precond = RPRef.sumOfFourthPowerOfOddNumbers n h_precond := by
  (try simp only [RPOrig.sumOfFourthPowerOfOddNumbers, RPRef.sumOfFourthPowerOfOddNumbers]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.sumOfFourthPowerOfOddNumbers RPRef.sumOfFourthPowerOfOddNumbers; rfl))
