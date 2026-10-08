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
private def cubeSurfaceArea__rp_helper_67e54167 (size : Nat) (h_precond : cubeSurfaceArea_precond (size)) : Nat :=
  6 * size * size

def cubeSurfaceArea (size : Nat) (h_precond : cubeSurfaceArea_precond (size)) : Nat :=
  cubeSurfaceArea__rp_helper_67e54167 size h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (size : Nat) (h_precond : cubeSurfaceArea_precond (size)) :
    RPOrig.cubeSurfaceArea size h_precond = RPRef.cubeSurfaceArea size h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (size : Nat) (h_precond : cubeSurfaceArea_precond (size)) :
    RPOrig.cubeSurfaceArea size h_precond = RPRef.cubeSurfaceArea size h_precond := rfl

theorem rp_equiv_delta_rfl (size : Nat) (h_precond : cubeSurfaceArea_precond (size)) :
    RPOrig.cubeSurfaceArea size h_precond = RPRef.cubeSurfaceArea size h_precond := by
  delta RPOrig.cubeSurfaceArea RPRef.cubeSurfaceArea RPRef.cubeSurfaceArea__rp_helper_67e54167
  rfl

theorem rp_equiv_simp_only (size : Nat) (h_precond : cubeSurfaceArea_precond (size)) :
    RPOrig.cubeSurfaceArea size h_precond = RPRef.cubeSurfaceArea size h_precond := by
  (simp only [RPOrig.cubeSurfaceArea, RPRef.cubeSurfaceArea, RPRef.cubeSurfaceArea__rp_helper_67e54167]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.cubeSurfaceArea RPRef.cubeSurfaceArea RPRef.cubeSurfaceArea__rp_helper_67e54167; rfl))

theorem rp_equiv_simp (size : Nat) (h_precond : cubeSurfaceArea_precond (size)) :
    RPOrig.cubeSurfaceArea size h_precond = RPRef.cubeSurfaceArea size h_precond := by
  (simp [RPOrig.cubeSurfaceArea, RPRef.cubeSurfaceArea, RPRef.cubeSurfaceArea__rp_helper_67e54167]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.cubeSurfaceArea RPRef.cubeSurfaceArea RPRef.cubeSurfaceArea__rp_helper_67e54167; rfl))
