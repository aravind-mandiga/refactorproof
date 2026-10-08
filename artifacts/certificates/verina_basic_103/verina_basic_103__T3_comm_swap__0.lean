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

def UpdateElements (a : Array Int) (h_precond : UpdateElements_precond (a)) : Array Int :=
  let a1 := a.set! 4 (3 + (a[4]!))
  let a2 := a1.set! 7 516
  a2
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (h_precond : UpdateElements_precond (a)) :
    RPOrig.UpdateElements a h_precond = RPRef.UpdateElements a h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (h_precond : UpdateElements_precond (a)) :
    RPOrig.UpdateElements a h_precond = RPRef.UpdateElements a h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (h_precond : UpdateElements_precond (a)) :
    RPOrig.UpdateElements a h_precond = RPRef.UpdateElements a h_precond := by
  delta RPOrig.UpdateElements RPRef.UpdateElements
  rfl

theorem rp_equiv_simp_only (a : Array Int) (h_precond : UpdateElements_precond (a)) :
    RPOrig.UpdateElements a h_precond = RPRef.UpdateElements a h_precond := by
  first
    | (simp only [RPOrig.UpdateElements, RPRef.UpdateElements, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.UpdateElements RPRef.UpdateElements; rfl))
    | (simp only [RPOrig.UpdateElements, RPRef.UpdateElements, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.UpdateElements RPRef.UpdateElements; rfl))
    | (simp only [RPOrig.UpdateElements, RPRef.UpdateElements, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.UpdateElements RPRef.UpdateElements; rfl))
    | (simp only [RPOrig.UpdateElements, RPRef.UpdateElements]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.UpdateElements RPRef.UpdateElements; rfl))

theorem rp_equiv_simp (a : Array Int) (h_precond : UpdateElements_precond (a)) :
    RPOrig.UpdateElements a h_precond = RPRef.UpdateElements a h_precond := by
  first
    | (simp [RPOrig.UpdateElements, RPRef.UpdateElements, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.UpdateElements RPRef.UpdateElements; rfl))
    | (simp [RPOrig.UpdateElements, RPRef.UpdateElements, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.UpdateElements RPRef.UpdateElements; rfl))
    | (simp [RPOrig.UpdateElements, RPRef.UpdateElements, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.UpdateElements RPRef.UpdateElements; rfl))
    | (simp [RPOrig.UpdateElements, RPRef.UpdateElements]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.UpdateElements RPRef.UpdateElements; rfl))

theorem rp_equiv_ac_rfl (a : Array Int) (h_precond : UpdateElements_precond (a)) :
    RPOrig.UpdateElements a h_precond = RPRef.UpdateElements a h_precond := by
  (try simp only [RPOrig.UpdateElements, RPRef.UpdateElements]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.UpdateElements RPRef.UpdateElements; rfl))
