-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux
def isOdd (n : Int) : Bool :=
  n % 2 == 1
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isOddAtIndexOdd_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def isOddAtIndexOdd (a : Array Int) (h_precond : isOddAtIndexOdd_precond (a)) : Bool :=
  -- First create pairs of (index, value) for all elements in the array
  let indexedArray := a.mapIdx fun i x => (i, x)

  -- Check if all elements at odd indices are odd numbers
  indexedArray.all fun (i, x) => !(isOdd i) || isOdd x
end RPOrig

namespace RPRef

def isOddAtIndexOdd (a : Array Int) (h_precond : isOddAtIndexOdd_precond (a)) : Bool :=
  let __rp_tmp_6b825f66 : Bool :=
    -- First create pairs of (index, value) for all elements in the array
    let indexedArray := a.mapIdx fun i x => (i, x)

    -- Check if all elements at odd indices are odd numbers
    indexedArray.all fun (i, x) => !(isOdd i) || isOdd x
  __rp_tmp_6b825f66
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (h_precond : isOddAtIndexOdd_precond (a)) :
    RPOrig.isOddAtIndexOdd a h_precond = RPRef.isOddAtIndexOdd a h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (h_precond : isOddAtIndexOdd_precond (a)) :
    RPOrig.isOddAtIndexOdd a h_precond = RPRef.isOddAtIndexOdd a h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (h_precond : isOddAtIndexOdd_precond (a)) :
    RPOrig.isOddAtIndexOdd a h_precond = RPRef.isOddAtIndexOdd a h_precond := by
  delta RPOrig.isOddAtIndexOdd RPRef.isOddAtIndexOdd
  rfl

theorem rp_equiv_simp_only (a : Array Int) (h_precond : isOddAtIndexOdd_precond (a)) :
    RPOrig.isOddAtIndexOdd a h_precond = RPRef.isOddAtIndexOdd a h_precond := by
  (simp only [RPOrig.isOddAtIndexOdd, RPRef.isOddAtIndexOdd]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isOddAtIndexOdd RPRef.isOddAtIndexOdd; rfl))

theorem rp_equiv_simp (a : Array Int) (h_precond : isOddAtIndexOdd_precond (a)) :
    RPOrig.isOddAtIndexOdd a h_precond = RPRef.isOddAtIndexOdd a h_precond := by
  (simp [RPOrig.isOddAtIndexOdd, RPRef.isOddAtIndexOdd]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isOddAtIndexOdd RPRef.isOddAtIndexOdd; rfl))
