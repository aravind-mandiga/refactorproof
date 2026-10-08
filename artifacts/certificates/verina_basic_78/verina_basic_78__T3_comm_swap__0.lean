-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def MultipleReturns_precond (x : Int) (y : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def MultipleReturns (x : Int) (y : Int) (h_precond : MultipleReturns_precond (x) (y)) : (Int × Int) :=
  let more := x + y
  let less := x - y
  (more, less)
end RPOrig

namespace RPRef

def MultipleReturns (x : Int) (y : Int) (h_precond : MultipleReturns_precond (x) (y)) : (Int × Int) :=
  let more := y + x
  let less := x - y
  (more, less)
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (x : Int) (y : Int) (h_precond : MultipleReturns_precond (x) (y)) :
    RPOrig.MultipleReturns x y h_precond = RPRef.MultipleReturns x y h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (x : Int) (y : Int) (h_precond : MultipleReturns_precond (x) (y)) :
    RPOrig.MultipleReturns x y h_precond = RPRef.MultipleReturns x y h_precond := rfl

theorem rp_equiv_delta_rfl (x : Int) (y : Int) (h_precond : MultipleReturns_precond (x) (y)) :
    RPOrig.MultipleReturns x y h_precond = RPRef.MultipleReturns x y h_precond := by
  delta RPOrig.MultipleReturns RPRef.MultipleReturns
  rfl

theorem rp_equiv_simp_only (x : Int) (y : Int) (h_precond : MultipleReturns_precond (x) (y)) :
    RPOrig.MultipleReturns x y h_precond = RPRef.MultipleReturns x y h_precond := by
  first
    | (simp only [RPOrig.MultipleReturns, RPRef.MultipleReturns, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.MultipleReturns RPRef.MultipleReturns; rfl))
    | (simp only [RPOrig.MultipleReturns, RPRef.MultipleReturns, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.MultipleReturns RPRef.MultipleReturns; rfl))
    | (simp only [RPOrig.MultipleReturns, RPRef.MultipleReturns, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.MultipleReturns RPRef.MultipleReturns; rfl))
    | (simp only [RPOrig.MultipleReturns, RPRef.MultipleReturns]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.MultipleReturns RPRef.MultipleReturns; rfl))

theorem rp_equiv_simp (x : Int) (y : Int) (h_precond : MultipleReturns_precond (x) (y)) :
    RPOrig.MultipleReturns x y h_precond = RPRef.MultipleReturns x y h_precond := by
  first
    | (simp [RPOrig.MultipleReturns, RPRef.MultipleReturns, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.MultipleReturns RPRef.MultipleReturns; rfl))
    | (simp [RPOrig.MultipleReturns, RPRef.MultipleReturns, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.MultipleReturns RPRef.MultipleReturns; rfl))
    | (simp [RPOrig.MultipleReturns, RPRef.MultipleReturns, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.MultipleReturns RPRef.MultipleReturns; rfl))
    | (simp [RPOrig.MultipleReturns, RPRef.MultipleReturns]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.MultipleReturns RPRef.MultipleReturns; rfl))

theorem rp_equiv_ac_rfl (x : Int) (y : Int) (h_precond : MultipleReturns_precond (x) (y)) :
    RPOrig.MultipleReturns x y h_precond = RPRef.MultipleReturns x y h_precond := by
  (try simp only [RPOrig.MultipleReturns, RPRef.MultipleReturns]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.MultipleReturns RPRef.MultipleReturns; rfl))
