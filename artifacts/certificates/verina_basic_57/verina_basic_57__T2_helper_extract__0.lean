-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def CountLessThan_precond (numbers : Array Int) (threshold : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def countLessThan (numbers : Array Int) (threshold : Int) : Nat :=
  let rec count (i : Nat) (acc : Nat) : Nat :=
    if i < numbers.size then
      let new_acc := if numbers[i]! < threshold then acc + 1 else acc
      count (i + 1) new_acc
    else
      acc
  count 0 0

namespace RPOrig

def CountLessThan (numbers : Array Int) (threshold : Int) (h_precond : CountLessThan_precond (numbers) (threshold)) : Nat :=
  countLessThan numbers threshold
end RPOrig

namespace RPRef

private def CountLessThan__rp_helper_29ea1684 (numbers : Array Int) (threshold : Int) (h_precond : CountLessThan_precond (numbers) (threshold)) : Nat :=
  countLessThan numbers threshold

def CountLessThan (numbers : Array Int) (threshold : Int) (h_precond : CountLessThan_precond (numbers) (threshold)) : Nat :=
  CountLessThan__rp_helper_29ea1684 numbers threshold h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (numbers : Array Int) (threshold : Int) (h_precond : CountLessThan_precond (numbers) (threshold)) :
    RPOrig.CountLessThan numbers threshold h_precond = RPRef.CountLessThan numbers threshold h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (numbers : Array Int) (threshold : Int) (h_precond : CountLessThan_precond (numbers) (threshold)) :
    RPOrig.CountLessThan numbers threshold h_precond = RPRef.CountLessThan numbers threshold h_precond := rfl

theorem rp_equiv_delta_rfl (numbers : Array Int) (threshold : Int) (h_precond : CountLessThan_precond (numbers) (threshold)) :
    RPOrig.CountLessThan numbers threshold h_precond = RPRef.CountLessThan numbers threshold h_precond := by
  delta RPOrig.CountLessThan RPRef.CountLessThan RPRef.CountLessThan__rp_helper_29ea1684
  rfl

theorem rp_equiv_simp_only (numbers : Array Int) (threshold : Int) (h_precond : CountLessThan_precond (numbers) (threshold)) :
    RPOrig.CountLessThan numbers threshold h_precond = RPRef.CountLessThan numbers threshold h_precond := by
  (simp only [RPOrig.CountLessThan, RPRef.CountLessThan, RPRef.CountLessThan__rp_helper_29ea1684]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.CountLessThan RPRef.CountLessThan RPRef.CountLessThan__rp_helper_29ea1684; rfl))

theorem rp_equiv_simp (numbers : Array Int) (threshold : Int) (h_precond : CountLessThan_precond (numbers) (threshold)) :
    RPOrig.CountLessThan numbers threshold h_precond = RPRef.CountLessThan numbers threshold h_precond := by
  (simp [RPOrig.CountLessThan, RPRef.CountLessThan, RPRef.CountLessThan__rp_helper_29ea1684]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.CountLessThan RPRef.CountLessThan RPRef.CountLessThan__rp_helper_29ea1684; rfl))
