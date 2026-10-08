-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def multiply_precond (a : Int) (b : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def multiply (a : Int) (b : Int) (h_precond : multiply_precond (a) (b)) : Int :=
  a * b
end RPOrig

namespace RPRef

def multiply (a : Int) (b : Int) (h_precond : multiply_precond (a) (b)) : Int :=
  b * a
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Int) (b : Int) (h_precond : multiply_precond (a) (b)) :
    RPOrig.multiply a b h_precond = RPRef.multiply a b h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Int) (b : Int) (h_precond : multiply_precond (a) (b)) :
    RPOrig.multiply a b h_precond = RPRef.multiply a b h_precond := rfl

theorem rp_equiv_delta_rfl (a : Int) (b : Int) (h_precond : multiply_precond (a) (b)) :
    RPOrig.multiply a b h_precond = RPRef.multiply a b h_precond := by
  delta RPOrig.multiply RPRef.multiply
  rfl

theorem rp_equiv_simp_only (a : Int) (b : Int) (h_precond : multiply_precond (a) (b)) :
    RPOrig.multiply a b h_precond = RPRef.multiply a b h_precond := by
  first
    | (simp only [RPOrig.multiply, RPRef.multiply, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.multiply RPRef.multiply; rfl))
    | (simp only [RPOrig.multiply, RPRef.multiply, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.multiply RPRef.multiply; rfl))
    | (simp only [RPOrig.multiply, RPRef.multiply, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.multiply RPRef.multiply; rfl))
    | (simp only [RPOrig.multiply, RPRef.multiply]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.multiply RPRef.multiply; rfl))

theorem rp_equiv_simp (a : Int) (b : Int) (h_precond : multiply_precond (a) (b)) :
    RPOrig.multiply a b h_precond = RPRef.multiply a b h_precond := by
  first
    | (simp [RPOrig.multiply, RPRef.multiply, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.multiply RPRef.multiply; rfl))
    | (simp [RPOrig.multiply, RPRef.multiply, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.multiply RPRef.multiply; rfl))
    | (simp [RPOrig.multiply, RPRef.multiply, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.multiply RPRef.multiply; rfl))
    | (simp [RPOrig.multiply, RPRef.multiply]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.multiply RPRef.multiply; rfl))

theorem rp_equiv_ac_rfl (a : Int) (b : Int) (h_precond : multiply_precond (a) (b)) :
    RPOrig.multiply a b h_precond = RPRef.multiply a b h_precond := by
  (try simp only [RPOrig.multiply, RPRef.multiply]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.multiply RPRef.multiply; rfl))
