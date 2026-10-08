-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def removeElement_precond (s : Array Int) (k : Nat) : Prop :=
  -- !benchmark @start precond
  k < s.size
  -- !benchmark @end precond



namespace RPOrig

def removeElement (s : Array Int) (k : Nat) (h_precond : removeElement_precond (s) (k)) : Array Int :=
  s.eraseIdx! k
end RPOrig

namespace RPRef
private def removeElement__rp_helper_718e0d1d (s : Array Int) (k : Nat) (h_precond : removeElement_precond (s) (k)) : Array Int :=
  s.eraseIdx! k

def removeElement (s : Array Int) (k : Nat) (h_precond : removeElement_precond (s) (k)) : Array Int :=
  removeElement__rp_helper_718e0d1d s k h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (s : Array Int) (k : Nat) (h_precond : removeElement_precond (s) (k)) :
    RPOrig.removeElement s k h_precond = RPRef.removeElement s k h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (s : Array Int) (k : Nat) (h_precond : removeElement_precond (s) (k)) :
    RPOrig.removeElement s k h_precond = RPRef.removeElement s k h_precond := rfl

theorem rp_equiv_delta_rfl (s : Array Int) (k : Nat) (h_precond : removeElement_precond (s) (k)) :
    RPOrig.removeElement s k h_precond = RPRef.removeElement s k h_precond := by
  delta RPOrig.removeElement RPRef.removeElement RPRef.removeElement__rp_helper_718e0d1d
  rfl

theorem rp_equiv_simp_only (s : Array Int) (k : Nat) (h_precond : removeElement_precond (s) (k)) :
    RPOrig.removeElement s k h_precond = RPRef.removeElement s k h_precond := by
  (simp only [RPOrig.removeElement, RPRef.removeElement, RPRef.removeElement__rp_helper_718e0d1d]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.removeElement RPRef.removeElement RPRef.removeElement__rp_helper_718e0d1d; rfl))

theorem rp_equiv_simp (s : Array Int) (k : Nat) (h_precond : removeElement_precond (s) (k)) :
    RPOrig.removeElement s k h_precond = RPRef.removeElement s k h_precond := by
  (simp [RPOrig.removeElement, RPRef.removeElement, RPRef.removeElement__rp_helper_718e0d1d]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.removeElement RPRef.removeElement RPRef.removeElement__rp_helper_718e0d1d; rfl))
