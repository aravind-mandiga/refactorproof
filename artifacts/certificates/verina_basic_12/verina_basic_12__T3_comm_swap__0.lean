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
  size * 6 * size
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
  first
    | (simp only [RPOrig.cubeSurfaceArea, RPRef.cubeSurfaceArea, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.cubeSurfaceArea RPRef.cubeSurfaceArea; rfl))
    | (simp only [RPOrig.cubeSurfaceArea, RPRef.cubeSurfaceArea, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.cubeSurfaceArea RPRef.cubeSurfaceArea; rfl))
    | (simp only [RPOrig.cubeSurfaceArea, RPRef.cubeSurfaceArea, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.cubeSurfaceArea RPRef.cubeSurfaceArea; rfl))
    | (simp only [RPOrig.cubeSurfaceArea, RPRef.cubeSurfaceArea]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.cubeSurfaceArea RPRef.cubeSurfaceArea; rfl))

theorem rp_equiv_simp (size : Nat) (h_precond : cubeSurfaceArea_precond (size)) :
    RPOrig.cubeSurfaceArea size h_precond = RPRef.cubeSurfaceArea size h_precond := by
  first
    | (simp [RPOrig.cubeSurfaceArea, RPRef.cubeSurfaceArea, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.cubeSurfaceArea RPRef.cubeSurfaceArea; rfl))
    | (simp [RPOrig.cubeSurfaceArea, RPRef.cubeSurfaceArea, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.cubeSurfaceArea RPRef.cubeSurfaceArea; rfl))
    | (simp [RPOrig.cubeSurfaceArea, RPRef.cubeSurfaceArea, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.cubeSurfaceArea RPRef.cubeSurfaceArea; rfl))
    | (simp [RPOrig.cubeSurfaceArea, RPRef.cubeSurfaceArea]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.cubeSurfaceArea RPRef.cubeSurfaceArea; rfl))

theorem rp_equiv_ac_rfl (size : Nat) (h_precond : cubeSurfaceArea_precond (size)) :
    RPOrig.cubeSurfaceArea size h_precond = RPRef.cubeSurfaceArea size h_precond := by
  (try simp only [RPOrig.cubeSurfaceArea, RPRef.cubeSurfaceArea]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.cubeSurfaceArea RPRef.cubeSurfaceArea; rfl))
