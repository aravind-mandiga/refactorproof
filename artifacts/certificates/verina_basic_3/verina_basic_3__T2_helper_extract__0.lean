-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isDivisibleBy11_precond (n : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def isDivisibleBy11 (n : Int) (h_precond : isDivisibleBy11_precond (n)) : Bool :=
  n % 11 == 0
end RPOrig

namespace RPRef
private def isDivisibleBy11__rp_helper_c39b37ae (n : Int) (h_precond : isDivisibleBy11_precond (n)) : Bool :=
  n % 11 == 0

def isDivisibleBy11 (n : Int) (h_precond : isDivisibleBy11_precond (n)) : Bool :=
  isDivisibleBy11__rp_helper_c39b37ae n h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (n : Int) (h_precond : isDivisibleBy11_precond (n)) :
    RPOrig.isDivisibleBy11 n h_precond = RPRef.isDivisibleBy11 n h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (n : Int) (h_precond : isDivisibleBy11_precond (n)) :
    RPOrig.isDivisibleBy11 n h_precond = RPRef.isDivisibleBy11 n h_precond := rfl

theorem rp_equiv_delta_rfl (n : Int) (h_precond : isDivisibleBy11_precond (n)) :
    RPOrig.isDivisibleBy11 n h_precond = RPRef.isDivisibleBy11 n h_precond := by
  delta RPOrig.isDivisibleBy11 RPRef.isDivisibleBy11 RPRef.isDivisibleBy11__rp_helper_c39b37ae
  rfl

theorem rp_equiv_simp_only (n : Int) (h_precond : isDivisibleBy11_precond (n)) :
    RPOrig.isDivisibleBy11 n h_precond = RPRef.isDivisibleBy11 n h_precond := by
  (simp only [RPOrig.isDivisibleBy11, RPRef.isDivisibleBy11, RPRef.isDivisibleBy11__rp_helper_c39b37ae]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isDivisibleBy11 RPRef.isDivisibleBy11 RPRef.isDivisibleBy11__rp_helper_c39b37ae; rfl))

theorem rp_equiv_simp (n : Int) (h_precond : isDivisibleBy11_precond (n)) :
    RPOrig.isDivisibleBy11 n h_precond = RPRef.isDivisibleBy11 n h_precond := by
  (simp [RPOrig.isDivisibleBy11, RPRef.isDivisibleBy11, RPRef.isDivisibleBy11__rp_helper_c39b37ae]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isDivisibleBy11 RPRef.isDivisibleBy11 RPRef.isDivisibleBy11__rp_helper_c39b37ae; rfl))
