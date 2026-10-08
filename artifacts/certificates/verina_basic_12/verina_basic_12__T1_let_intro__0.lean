-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def cubeSurfaceArea_precond (size : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def cubeSurfaceArea (size : Nat) (h_precond : cubeSurfaceArea_precond (size)) : Nat :=
  6 * size * size
end RPOrig

namespace RPRef

def cubeSurfaceArea (size : Nat) (h_precond : cubeSurfaceArea_precond (size)) : Nat :=
  let __rp_tmp_3e6b423e : Nat :=
    6 * size * size
  __rp_tmp_3e6b423e
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (size : Nat) (h_precond : cubeSurfaceArea_precond (size)) :
    RPOrig.cubeSurfaceArea size h_precond = RPRef.cubeSurfaceArea size h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (size : Nat) (h_precond : cubeSurfaceArea_precond (size)) :
    RPOrig.cubeSurfaceArea size h_precond = RPRef.cubeSurfaceArea size h_precond := rfl

theorem rp_equiv_delta_rfl (size : Nat) (h_precond : cubeSurfaceArea_precond (size)) :
    RPOrig.cubeSurfaceArea size h_precond = RPRef.cubeSurfaceArea size h_precond := by
  delta RPOrig.cubeSurfaceArea RPRef.cubeSurfaceArea
  rfl

theorem rp_equiv_simp_only (size : Nat) (h_precond : cubeSurfaceArea_precond (size)) :
    RPOrig.cubeSurfaceArea size h_precond = RPRef.cubeSurfaceArea size h_precond := by
  (simp only [RPOrig.cubeSurfaceArea, RPRef.cubeSurfaceArea]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.cubeSurfaceArea RPRef.cubeSurfaceArea; rfl))

theorem rp_equiv_simp (size : Nat) (h_precond : cubeSurfaceArea_precond (size)) :
    RPOrig.cubeSurfaceArea size h_precond = RPRef.cubeSurfaceArea size h_precond := by
  (simp [RPOrig.cubeSurfaceArea, RPRef.cubeSurfaceArea]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.cubeSurfaceArea RPRef.cubeSurfaceArea; rfl))
