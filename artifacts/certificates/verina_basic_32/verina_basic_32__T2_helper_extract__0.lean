-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start import type=llm
-- !benchmark @end import

-- !benchmark @start import type=test
-- !benchmark @end import

-- !benchmark @start solution_aux
-- !benchmark @end solution_aux
-- !benchmark @start precond_aux
-- !benchmark @end precond_aux

def swapFirstAndLast_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0
  -- !benchmark @end precond


namespace RPOrig

def swapFirstAndLast (a : Array Int) (h_precond: swapFirstAndLast_precond a) : Array Int :=
  let first := a[0]!
  let last := a[a.size - 1]!
  a.set! 0 last |>.set! (a.size - 1) first
end RPOrig

namespace RPRef

private def swapFirstAndLast__rp_helper_6bb66f38 (a : Array Int) (h_precond: swapFirstAndLast_precond a) : Array Int :=
  let first := a[0]!
  let last := a[a.size - 1]!
  a.set! 0 last |>.set! (a.size - 1) first

def swapFirstAndLast (a : Array Int) (h_precond: swapFirstAndLast_precond a) : Array Int :=
  swapFirstAndLast__rp_helper_6bb66f38 a h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (h_precond: swapFirstAndLast_precond a) :
    RPOrig.swapFirstAndLast a h_precond = RPRef.swapFirstAndLast a h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (h_precond: swapFirstAndLast_precond a) :
    RPOrig.swapFirstAndLast a h_precond = RPRef.swapFirstAndLast a h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (h_precond: swapFirstAndLast_precond a) :
    RPOrig.swapFirstAndLast a h_precond = RPRef.swapFirstAndLast a h_precond := by
  delta RPOrig.swapFirstAndLast RPRef.swapFirstAndLast RPRef.swapFirstAndLast__rp_helper_6bb66f38
  rfl

theorem rp_equiv_simp_only (a : Array Int) (h_precond: swapFirstAndLast_precond a) :
    RPOrig.swapFirstAndLast a h_precond = RPRef.swapFirstAndLast a h_precond := by
  (simp only [RPOrig.swapFirstAndLast, RPRef.swapFirstAndLast, RPRef.swapFirstAndLast__rp_helper_6bb66f38]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.swapFirstAndLast RPRef.swapFirstAndLast RPRef.swapFirstAndLast__rp_helper_6bb66f38; rfl))

theorem rp_equiv_simp (a : Array Int) (h_precond: swapFirstAndLast_precond a) :
    RPOrig.swapFirstAndLast a h_precond = RPRef.swapFirstAndLast a h_precond := by
  (simp [RPOrig.swapFirstAndLast, RPRef.swapFirstAndLast, RPRef.swapFirstAndLast__rp_helper_6bb66f38]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.swapFirstAndLast RPRef.swapFirstAndLast RPRef.swapFirstAndLast__rp_helper_6bb66f38; rfl))
