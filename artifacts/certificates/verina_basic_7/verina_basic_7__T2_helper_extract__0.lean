-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def sumOfSquaresOfFirstNOddNumbers_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def sumOfSquaresOfFirstNOddNumbers (n : Nat) (h_precond : sumOfSquaresOfFirstNOddNumbers_precond (n)) : Nat :=
  let rec loop (k : Nat) (sum : Nat) : Nat :=
    if k = 0 then
      sum
    else
      loop (k - 1) (sum + (2 * k - 1) * (2 * k - 1))
  loop n 0
end RPOrig

namespace RPRef
private def sumOfSquaresOfFirstNOddNumbers__rp_helper_b01a7f4c (n : Nat) (h_precond : sumOfSquaresOfFirstNOddNumbers_precond (n)) : Nat :=
  let rec loop (k : Nat) (sum : Nat) : Nat :=
    if k = 0 then
      sum
    else
      loop (k - 1) (sum + (2 * k - 1) * (2 * k - 1))
  loop n 0

def sumOfSquaresOfFirstNOddNumbers (n : Nat) (h_precond : sumOfSquaresOfFirstNOddNumbers_precond (n)) : Nat :=
  sumOfSquaresOfFirstNOddNumbers__rp_helper_b01a7f4c n h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (n : Nat) (h_precond : sumOfSquaresOfFirstNOddNumbers_precond (n)) :
    RPOrig.sumOfSquaresOfFirstNOddNumbers n h_precond = RPRef.sumOfSquaresOfFirstNOddNumbers n h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (n : Nat) (h_precond : sumOfSquaresOfFirstNOddNumbers_precond (n)) :
    RPOrig.sumOfSquaresOfFirstNOddNumbers n h_precond = RPRef.sumOfSquaresOfFirstNOddNumbers n h_precond := rfl

theorem rp_equiv_delta_rfl (n : Nat) (h_precond : sumOfSquaresOfFirstNOddNumbers_precond (n)) :
    RPOrig.sumOfSquaresOfFirstNOddNumbers n h_precond = RPRef.sumOfSquaresOfFirstNOddNumbers n h_precond := by
  delta RPOrig.sumOfSquaresOfFirstNOddNumbers RPRef.sumOfSquaresOfFirstNOddNumbers RPRef.sumOfSquaresOfFirstNOddNumbers__rp_helper_b01a7f4c RPOrig.sumOfSquaresOfFirstNOddNumbers.loop RPRef.sumOfSquaresOfFirstNOddNumbers__rp_helper_b01a7f4c.loop
  rfl

theorem rp_equiv_simp_only (n : Nat) (h_precond : sumOfSquaresOfFirstNOddNumbers_precond (n)) :
    RPOrig.sumOfSquaresOfFirstNOddNumbers n h_precond = RPRef.sumOfSquaresOfFirstNOddNumbers n h_precond := by
  (simp only [RPOrig.sumOfSquaresOfFirstNOddNumbers, RPRef.sumOfSquaresOfFirstNOddNumbers, RPRef.sumOfSquaresOfFirstNOddNumbers__rp_helper_b01a7f4c]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.sumOfSquaresOfFirstNOddNumbers RPRef.sumOfSquaresOfFirstNOddNumbers RPRef.sumOfSquaresOfFirstNOddNumbers__rp_helper_b01a7f4c RPOrig.sumOfSquaresOfFirstNOddNumbers.loop RPRef.sumOfSquaresOfFirstNOddNumbers__rp_helper_b01a7f4c.loop; rfl))

theorem rp_equiv_simp (n : Nat) (h_precond : sumOfSquaresOfFirstNOddNumbers_precond (n)) :
    RPOrig.sumOfSquaresOfFirstNOddNumbers n h_precond = RPRef.sumOfSquaresOfFirstNOddNumbers n h_precond := by
  (simp [RPOrig.sumOfSquaresOfFirstNOddNumbers, RPRef.sumOfSquaresOfFirstNOddNumbers, RPRef.sumOfSquaresOfFirstNOddNumbers__rp_helper_b01a7f4c]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.sumOfSquaresOfFirstNOddNumbers RPRef.sumOfSquaresOfFirstNOddNumbers RPRef.sumOfSquaresOfFirstNOddNumbers__rp_helper_b01a7f4c RPOrig.sumOfSquaresOfFirstNOddNumbers.loop RPRef.sumOfSquaresOfFirstNOddNumbers__rp_helper_b01a7f4c.loop; rfl))
