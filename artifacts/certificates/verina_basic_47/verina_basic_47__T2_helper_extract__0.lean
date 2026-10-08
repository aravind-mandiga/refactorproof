-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def arraySum_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0
  -- !benchmark @end precond



namespace RPOrig

def arraySum (a : Array Int) (h_precond : arraySum_precond (a)) : Int :=
  a.toList.sum
end RPOrig

namespace RPRef
private def arraySum__rp_helper_4569da9e (a : Array Int) (h_precond : arraySum_precond (a)) : Int :=
  a.toList.sum

def arraySum (a : Array Int) (h_precond : arraySum_precond (a)) : Int :=
  arraySum__rp_helper_4569da9e a h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (h_precond : arraySum_precond (a)) :
    RPOrig.arraySum a h_precond = RPRef.arraySum a h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (h_precond : arraySum_precond (a)) :
    RPOrig.arraySum a h_precond = RPRef.arraySum a h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (h_precond : arraySum_precond (a)) :
    RPOrig.arraySum a h_precond = RPRef.arraySum a h_precond := by
  delta RPOrig.arraySum RPRef.arraySum RPRef.arraySum__rp_helper_4569da9e
  rfl

theorem rp_equiv_simp_only (a : Array Int) (h_precond : arraySum_precond (a)) :
    RPOrig.arraySum a h_precond = RPRef.arraySum a h_precond := by
  (simp only [RPOrig.arraySum, RPRef.arraySum, RPRef.arraySum__rp_helper_4569da9e]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.arraySum RPRef.arraySum RPRef.arraySum__rp_helper_4569da9e; rfl))

theorem rp_equiv_simp (a : Array Int) (h_precond : arraySum_precond (a)) :
    RPOrig.arraySum a h_precond = RPRef.arraySum a h_precond := by
  (simp [RPOrig.arraySum, RPRef.arraySum, RPRef.arraySum__rp_helper_4569da9e]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.arraySum RPRef.arraySum RPRef.arraySum__rp_helper_4569da9e; rfl))
