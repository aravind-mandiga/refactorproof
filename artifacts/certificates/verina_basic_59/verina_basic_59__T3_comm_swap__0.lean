-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def DoubleQuadruple_precond (x : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def DoubleQuadruple (x : Int) (h_precond : DoubleQuadruple_precond (x)) : (Int × Int) :=
  let a := 2 * x
  let b := 2 * a
  (a, b)
end RPOrig

namespace RPRef

def DoubleQuadruple (x : Int) (h_precond : DoubleQuadruple_precond (x)) : (Int × Int) :=
  let a := x * 2
  let b := 2 * a
  (a, b)
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (x : Int) (h_precond : DoubleQuadruple_precond (x)) :
    RPOrig.DoubleQuadruple x h_precond = RPRef.DoubleQuadruple x h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (x : Int) (h_precond : DoubleQuadruple_precond (x)) :
    RPOrig.DoubleQuadruple x h_precond = RPRef.DoubleQuadruple x h_precond := rfl

theorem rp_equiv_delta_rfl (x : Int) (h_precond : DoubleQuadruple_precond (x)) :
    RPOrig.DoubleQuadruple x h_precond = RPRef.DoubleQuadruple x h_precond := by
  delta RPOrig.DoubleQuadruple RPRef.DoubleQuadruple
  rfl

theorem rp_equiv_simp_only (x : Int) (h_precond : DoubleQuadruple_precond (x)) :
    RPOrig.DoubleQuadruple x h_precond = RPRef.DoubleQuadruple x h_precond := by
  first
    | (simp only [RPOrig.DoubleQuadruple, RPRef.DoubleQuadruple, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.DoubleQuadruple RPRef.DoubleQuadruple; rfl))
    | (simp only [RPOrig.DoubleQuadruple, RPRef.DoubleQuadruple, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.DoubleQuadruple RPRef.DoubleQuadruple; rfl))
    | (simp only [RPOrig.DoubleQuadruple, RPRef.DoubleQuadruple, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.DoubleQuadruple RPRef.DoubleQuadruple; rfl))
    | (simp only [RPOrig.DoubleQuadruple, RPRef.DoubleQuadruple]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.DoubleQuadruple RPRef.DoubleQuadruple; rfl))

theorem rp_equiv_simp (x : Int) (h_precond : DoubleQuadruple_precond (x)) :
    RPOrig.DoubleQuadruple x h_precond = RPRef.DoubleQuadruple x h_precond := by
  first
    | (simp [RPOrig.DoubleQuadruple, RPRef.DoubleQuadruple, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.DoubleQuadruple RPRef.DoubleQuadruple; rfl))
    | (simp [RPOrig.DoubleQuadruple, RPRef.DoubleQuadruple, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.DoubleQuadruple RPRef.DoubleQuadruple; rfl))
    | (simp [RPOrig.DoubleQuadruple, RPRef.DoubleQuadruple, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.DoubleQuadruple RPRef.DoubleQuadruple; rfl))
    | (simp [RPOrig.DoubleQuadruple, RPRef.DoubleQuadruple]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.DoubleQuadruple RPRef.DoubleQuadruple; rfl))

theorem rp_equiv_ac_rfl (x : Int) (h_precond : DoubleQuadruple_precond (x)) :
    RPOrig.DoubleQuadruple x h_precond = RPRef.DoubleQuadruple x h_precond := by
  (try simp only [RPOrig.DoubleQuadruple, RPRef.DoubleQuadruple]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.DoubleQuadruple RPRef.DoubleQuadruple; rfl))
