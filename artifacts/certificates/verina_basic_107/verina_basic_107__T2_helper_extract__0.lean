-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def ComputeAvg_precond (a : Int) (b : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def ComputeAvg (a : Int) (b : Int) (h_precond : ComputeAvg_precond (a) (b)) : Int :=
  (a + b) / 2
end RPOrig

namespace RPRef
private def ComputeAvg__rp_helper_860051f2 (a : Int) (b : Int) (h_precond : ComputeAvg_precond (a) (b)) : Int :=
  (a + b) / 2

def ComputeAvg (a : Int) (b : Int) (h_precond : ComputeAvg_precond (a) (b)) : Int :=
  ComputeAvg__rp_helper_860051f2 a b h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Int) (b : Int) (h_precond : ComputeAvg_precond (a) (b)) :
    RPOrig.ComputeAvg a b h_precond = RPRef.ComputeAvg a b h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Int) (b : Int) (h_precond : ComputeAvg_precond (a) (b)) :
    RPOrig.ComputeAvg a b h_precond = RPRef.ComputeAvg a b h_precond := rfl

theorem rp_equiv_delta_rfl (a : Int) (b : Int) (h_precond : ComputeAvg_precond (a) (b)) :
    RPOrig.ComputeAvg a b h_precond = RPRef.ComputeAvg a b h_precond := by
  delta RPOrig.ComputeAvg RPRef.ComputeAvg RPRef.ComputeAvg__rp_helper_860051f2
  rfl

theorem rp_equiv_simp_only (a : Int) (b : Int) (h_precond : ComputeAvg_precond (a) (b)) :
    RPOrig.ComputeAvg a b h_precond = RPRef.ComputeAvg a b h_precond := by
  (simp only [RPOrig.ComputeAvg, RPRef.ComputeAvg, RPRef.ComputeAvg__rp_helper_860051f2]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.ComputeAvg RPRef.ComputeAvg RPRef.ComputeAvg__rp_helper_860051f2; rfl))

theorem rp_equiv_simp (a : Int) (b : Int) (h_precond : ComputeAvg_precond (a) (b)) :
    RPOrig.ComputeAvg a b h_precond = RPRef.ComputeAvg a b h_precond := by
  (simp [RPOrig.ComputeAvg, RPRef.ComputeAvg, RPRef.ComputeAvg__rp_helper_860051f2]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.ComputeAvg RPRef.ComputeAvg RPRef.ComputeAvg__rp_helper_860051f2; rfl))
