-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def SwapArithmetic_precond (X : Int) (Y : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def SwapArithmetic (X : Int) (Y : Int) (h_precond : SwapArithmetic_precond (X) (Y)) : (Int × Int) :=
  let x1 := X
  let y1 := Y
  let x2 := y1 - x1
  let y2 := y1 - x2
  let x3 := y2 + x2
  (x3, y2)
end RPOrig

namespace RPRef

def SwapArithmetic (X : Int) (Y : Int) (h_precond : SwapArithmetic_precond (X) (Y)) : (Int × Int) :=
  let x1 := X
  let y1 := Y
  let x2 := y1 - x1
  let y2 := y1 - x2
  let x3 := x2 + y2
  (x3, y2)
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (X : Int) (Y : Int) (h_precond : SwapArithmetic_precond (X) (Y)) :
    RPOrig.SwapArithmetic X Y h_precond = RPRef.SwapArithmetic X Y h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (X : Int) (Y : Int) (h_precond : SwapArithmetic_precond (X) (Y)) :
    RPOrig.SwapArithmetic X Y h_precond = RPRef.SwapArithmetic X Y h_precond := rfl

theorem rp_equiv_delta_rfl (X : Int) (Y : Int) (h_precond : SwapArithmetic_precond (X) (Y)) :
    RPOrig.SwapArithmetic X Y h_precond = RPRef.SwapArithmetic X Y h_precond := by
  delta RPOrig.SwapArithmetic RPRef.SwapArithmetic
  rfl

theorem rp_equiv_simp_only (X : Int) (Y : Int) (h_precond : SwapArithmetic_precond (X) (Y)) :
    RPOrig.SwapArithmetic X Y h_precond = RPRef.SwapArithmetic X Y h_precond := by
  first
    | (simp only [RPOrig.SwapArithmetic, RPRef.SwapArithmetic, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SwapArithmetic RPRef.SwapArithmetic; rfl))
    | (simp only [RPOrig.SwapArithmetic, RPRef.SwapArithmetic, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SwapArithmetic RPRef.SwapArithmetic; rfl))
    | (simp only [RPOrig.SwapArithmetic, RPRef.SwapArithmetic, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SwapArithmetic RPRef.SwapArithmetic; rfl))
    | (simp only [RPOrig.SwapArithmetic, RPRef.SwapArithmetic]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SwapArithmetic RPRef.SwapArithmetic; rfl))

theorem rp_equiv_simp (X : Int) (Y : Int) (h_precond : SwapArithmetic_precond (X) (Y)) :
    RPOrig.SwapArithmetic X Y h_precond = RPRef.SwapArithmetic X Y h_precond := by
  first
    | (simp [RPOrig.SwapArithmetic, RPRef.SwapArithmetic, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SwapArithmetic RPRef.SwapArithmetic; rfl))
    | (simp [RPOrig.SwapArithmetic, RPRef.SwapArithmetic, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SwapArithmetic RPRef.SwapArithmetic; rfl))
    | (simp [RPOrig.SwapArithmetic, RPRef.SwapArithmetic, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SwapArithmetic RPRef.SwapArithmetic; rfl))
    | (simp [RPOrig.SwapArithmetic, RPRef.SwapArithmetic]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SwapArithmetic RPRef.SwapArithmetic; rfl))

theorem rp_equiv_ac_rfl (X : Int) (Y : Int) (h_precond : SwapArithmetic_precond (X) (Y)) :
    RPOrig.SwapArithmetic X Y h_precond = RPRef.SwapArithmetic X Y h_precond := by
  (try simp only [RPOrig.SwapArithmetic, RPRef.SwapArithmetic]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SwapArithmetic RPRef.SwapArithmetic; rfl))
