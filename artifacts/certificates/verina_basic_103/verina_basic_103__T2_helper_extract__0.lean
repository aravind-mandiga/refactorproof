-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def UpdateElements_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size ≥ 8
  -- !benchmark @end precond



namespace RPOrig

def UpdateElements (a : Array Int) (h_precond : UpdateElements_precond (a)) : Array Int :=
  let a1 := a.set! 4 ((a[4]!) + 3)
  let a2 := a1.set! 7 516
  a2
end RPOrig

namespace RPRef
private def UpdateElements__rp_helper_b80f086d (a : Array Int) (h_precond : UpdateElements_precond (a)) : Array Int :=
  let a1 := a.set! 4 ((a[4]!) + 3)
  let a2 := a1.set! 7 516
  a2

def UpdateElements (a : Array Int) (h_precond : UpdateElements_precond (a)) : Array Int :=
  UpdateElements__rp_helper_b80f086d a h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (h_precond : UpdateElements_precond (a)) :
    RPOrig.UpdateElements a h_precond = RPRef.UpdateElements a h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (h_precond : UpdateElements_precond (a)) :
    RPOrig.UpdateElements a h_precond = RPRef.UpdateElements a h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (h_precond : UpdateElements_precond (a)) :
    RPOrig.UpdateElements a h_precond = RPRef.UpdateElements a h_precond := by
  delta RPOrig.UpdateElements RPRef.UpdateElements RPRef.UpdateElements__rp_helper_b80f086d
  rfl

theorem rp_equiv_simp_only (a : Array Int) (h_precond : UpdateElements_precond (a)) :
    RPOrig.UpdateElements a h_precond = RPRef.UpdateElements a h_precond := by
  (simp only [RPOrig.UpdateElements, RPRef.UpdateElements, RPRef.UpdateElements__rp_helper_b80f086d]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.UpdateElements RPRef.UpdateElements RPRef.UpdateElements__rp_helper_b80f086d; rfl))

theorem rp_equiv_simp (a : Array Int) (h_precond : UpdateElements_precond (a)) :
    RPOrig.UpdateElements a h_precond = RPRef.UpdateElements a h_precond := by
  (simp [RPOrig.UpdateElements, RPRef.UpdateElements, RPRef.UpdateElements__rp_helper_b80f086d]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.UpdateElements RPRef.UpdateElements RPRef.UpdateElements__rp_helper_b80f086d; rfl))
