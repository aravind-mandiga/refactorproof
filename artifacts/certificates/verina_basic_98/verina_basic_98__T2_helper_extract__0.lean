-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def Triple_precond (x : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def Triple (x : Int) (h_precond : Triple_precond (x)) : Int :=
  x * 3
end RPOrig

namespace RPRef
private def Triple__rp_helper_c4a61f58 (x : Int) (h_precond : Triple_precond (x)) : Int :=
  x * 3

def Triple (x : Int) (h_precond : Triple_precond (x)) : Int :=
  Triple__rp_helper_c4a61f58 x h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (x : Int) (h_precond : Triple_precond (x)) :
    RPOrig.Triple x h_precond = RPRef.Triple x h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (x : Int) (h_precond : Triple_precond (x)) :
    RPOrig.Triple x h_precond = RPRef.Triple x h_precond := rfl

theorem rp_equiv_delta_rfl (x : Int) (h_precond : Triple_precond (x)) :
    RPOrig.Triple x h_precond = RPRef.Triple x h_precond := by
  delta RPOrig.Triple RPRef.Triple RPRef.Triple__rp_helper_c4a61f58
  rfl

theorem rp_equiv_simp_only (x : Int) (h_precond : Triple_precond (x)) :
    RPOrig.Triple x h_precond = RPRef.Triple x h_precond := by
  (simp only [RPOrig.Triple, RPRef.Triple, RPRef.Triple__rp_helper_c4a61f58]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Triple RPRef.Triple RPRef.Triple__rp_helper_c4a61f58; rfl))

theorem rp_equiv_simp (x : Int) (h_precond : Triple_precond (x)) :
    RPOrig.Triple x h_precond = RPRef.Triple x h_precond := by
  (simp [RPOrig.Triple, RPRef.Triple, RPRef.Triple__rp_helper_c4a61f58]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Triple RPRef.Triple RPRef.Triple__rp_helper_c4a61f58; rfl))
