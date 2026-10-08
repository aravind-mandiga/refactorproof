-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start task_aux
-- Lean 4's Float is an opaque C FFI type with no kernel lemmas.
-- These axioms capture IEEE 754-compliant behavior for non-NaN/non-Inf floats.
axiom Float.not_isNaN_ofNat (n : Nat) : (n.toFloat).isNaN = false
axiom Float.isFinite_ofNat (n : Nat) (h : n < 2 ^ 53) :
    (n.toFloat).isNaN = false ∧ (n.toFloat).isInf = false
axiom Float.ofNat_beq_zero_false (n : Nat) (h : 0 < n) :
    (n.toFloat == (0 : Float)) = false
axiom Float.beq_self_of_not_isNaN (x : Float) (h : x.isNaN = false) :
    (x == x) = true
axiom Float.not_isNaN_sub (x y : Float)
    (hx : x.isNaN = false) (hy : y.isNaN = false)
    (hx_inf : x.isInf = false) (hy_inf : y.isInf = false) :
    (x - y).isNaN = false
axiom Float.not_isNaN_div (x y : Float)
    (hx : x.isNaN = false) (hy : y.isNaN = false)
    (hy0 : (y == 0) = false) (hinf : x.isInf = false ∨ y.isInf = false) :
    (x / y).isNaN = false
axiom Float.le_total_of_not_isNaN (x y : Float)
    (hx : x.isNaN = false) (hy : y.isNaN = false) :
    x ≤ y ∨ y ≤ x
axiom Float.lt_iff_le_not_le_of_not_isNaN (x y : Float)
    (hx : x.isNaN = false) (hy : y.isNaN = false) :
    x < y ↔ x ≤ y ∧ ¬ y ≤ x
-- !benchmark @end task_aux

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def sumAndAverage_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  n > 0 ∧ n < 9007199254740992  -- n must be positive and bounded for Float precision
  -- !benchmark @end precond



namespace RPOrig

def sumAndAverage (n : Nat) (h_precond : sumAndAverage_precond (n)) : Int × Float :=
  if n ≤ 0 then (0, 0.0)
  else
    let sum := (List.range (n + 1)).sum
    let average : Float := sum.toFloat / (n.toFloat)
    (sum, average)
end RPOrig

namespace RPRef

def sumAndAverage (n : Nat) (h_precond : sumAndAverage_precond (n)) : Int × Float :=
  if n ≤ 0 then (0, 0.0)
  else
    let sum := (List.range (1 + n)).sum
    let average : Float := sum.toFloat / (n.toFloat)
    (sum, average)
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (n : Nat) (h_precond : sumAndAverage_precond (n)) :
    RPOrig.sumAndAverage n h_precond = RPRef.sumAndAverage n h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (n : Nat) (h_precond : sumAndAverage_precond (n)) :
    RPOrig.sumAndAverage n h_precond = RPRef.sumAndAverage n h_precond := rfl

theorem rp_equiv_delta_rfl (n : Nat) (h_precond : sumAndAverage_precond (n)) :
    RPOrig.sumAndAverage n h_precond = RPRef.sumAndAverage n h_precond := by
  delta RPOrig.sumAndAverage RPRef.sumAndAverage
  rfl

theorem rp_equiv_simp_only (n : Nat) (h_precond : sumAndAverage_precond (n)) :
    RPOrig.sumAndAverage n h_precond = RPRef.sumAndAverage n h_precond := by
  first
    | (simp only [RPOrig.sumAndAverage, RPRef.sumAndAverage, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.sumAndAverage RPRef.sumAndAverage; rfl))
    | (simp only [RPOrig.sumAndAverage, RPRef.sumAndAverage, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.sumAndAverage RPRef.sumAndAverage; rfl))
    | (simp only [RPOrig.sumAndAverage, RPRef.sumAndAverage, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.sumAndAverage RPRef.sumAndAverage; rfl))
    | (simp only [RPOrig.sumAndAverage, RPRef.sumAndAverage]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.sumAndAverage RPRef.sumAndAverage; rfl))

theorem rp_equiv_simp (n : Nat) (h_precond : sumAndAverage_precond (n)) :
    RPOrig.sumAndAverage n h_precond = RPRef.sumAndAverage n h_precond := by
  first
    | (simp [RPOrig.sumAndAverage, RPRef.sumAndAverage, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.sumAndAverage RPRef.sumAndAverage; rfl))
    | (simp [RPOrig.sumAndAverage, RPRef.sumAndAverage, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.sumAndAverage RPRef.sumAndAverage; rfl))
    | (simp [RPOrig.sumAndAverage, RPRef.sumAndAverage, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.sumAndAverage RPRef.sumAndAverage; rfl))
    | (simp [RPOrig.sumAndAverage, RPRef.sumAndAverage]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.sumAndAverage RPRef.sumAndAverage; rfl))

theorem rp_equiv_ac_rfl (n : Nat) (h_precond : sumAndAverage_precond (n)) :
    RPOrig.sumAndAverage n h_precond = RPRef.sumAndAverage n h_precond := by
  (try simp only [RPOrig.sumAndAverage, RPRef.sumAndAverage]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.sumAndAverage RPRef.sumAndAverage; rfl))
