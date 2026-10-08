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
  let __rp_tmp_6abd56c6 : Nat :=
    match n with
    | 0 => 0
    | n + 1 =>
      let prev := sumOfFourthPowerOfOddNumbers n h_precond
      let nextOdd := 2 * n + 1
      prev + nextOdd^4
  __rp_tmp_6abd56c6
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
  (simp only [RPOrig.sumOfFourthPowerOfOddNumbers, RPRef.sumOfFourthPowerOfOddNumbers]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.sumOfFourthPowerOfOddNumbers RPRef.sumOfFourthPowerOfOddNumbers; rfl))

theorem rp_equiv_simp (n : Nat) (h_precond : sumOfFourthPowerOfOddNumbers_precond (n)) :
    RPOrig.sumOfFourthPowerOfOddNumbers n h_precond = RPRef.sumOfFourthPowerOfOddNumbers n h_precond := by
  (simp [RPOrig.sumOfFourthPowerOfOddNumbers, RPRef.sumOfFourthPowerOfOddNumbers]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.sumOfFourthPowerOfOddNumbers RPRef.sumOfFourthPowerOfOddNumbers; rfl))
