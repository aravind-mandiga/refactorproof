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
private def sumAndAverage__rp_helper_1602f4f3 (n : Nat) (h_precond : sumAndAverage_precond (n)) : Int × Float :=
  if n ≤ 0 then (0, 0.0)
  else
    let sum := (List.range (n + 1)).sum
    let average : Float := sum.toFloat / (n.toFloat)
    (sum, average)

def sumAndAverage (n : Nat) (h_precond : sumAndAverage_precond (n)) : Int × Float :=
  sumAndAverage__rp_helper_1602f4f3 n h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (n : Nat) (h_precond : sumAndAverage_precond (n)) :
    RPOrig.sumAndAverage n h_precond = RPRef.sumAndAverage n h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (n : Nat) (h_precond : sumAndAverage_precond (n)) :
    RPOrig.sumAndAverage n h_precond = RPRef.sumAndAverage n h_precond := rfl

theorem rp_equiv_delta_rfl (n : Nat) (h_precond : sumAndAverage_precond (n)) :
    RPOrig.sumAndAverage n h_precond = RPRef.sumAndAverage n h_precond := by
  delta RPOrig.sumAndAverage RPRef.sumAndAverage RPRef.sumAndAverage__rp_helper_1602f4f3
  rfl

theorem rp_equiv_simp_only (n : Nat) (h_precond : sumAndAverage_precond (n)) :
    RPOrig.sumAndAverage n h_precond = RPRef.sumAndAverage n h_precond := by
  (simp only [RPOrig.sumAndAverage, RPRef.sumAndAverage, RPRef.sumAndAverage__rp_helper_1602f4f3]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.sumAndAverage RPRef.sumAndAverage RPRef.sumAndAverage__rp_helper_1602f4f3; rfl))

theorem rp_equiv_simp (n : Nat) (h_precond : sumAndAverage_precond (n)) :
    RPOrig.sumAndAverage n h_precond = RPRef.sumAndAverage n h_precond := by
  (simp [RPOrig.sumAndAverage, RPRef.sumAndAverage, RPRef.sumAndAverage__rp_helper_1602f4f3]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.sumAndAverage RPRef.sumAndAverage RPRef.sumAndAverage__rp_helper_1602f4f3; rfl))
