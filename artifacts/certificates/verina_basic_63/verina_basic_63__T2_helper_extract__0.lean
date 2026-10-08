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
def absDiff (a b : Float) : Float :=
  if a - b < 0.0 then b - a else a - b
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def has_close_elements_precond (numbers : List Float) (threshold : Float) : Prop :=
  -- !benchmark @start precond
  threshold ≥ 0.0 ∧
  ¬threshold.isNaN ∧
  numbers.all (fun x => ¬x.isNaN ∧ ¬x.isInf)  -- no NaN or Inf values
  -- !benchmark @end precond



namespace RPOrig

def has_close_elements (numbers : List Float) (threshold : Float) (h_precond : has_close_elements_precond (numbers) (threshold)) : Bool :=
  let len := numbers.length
  let rec outer (idx : Nat) : Bool :=
    if idx < len then
      let rec inner (idx2 : Nat) : Bool :=
        if idx2 < idx then
          let a := numbers.getD idx2 0.0
          let b := numbers.getD idx 0.0
          let d := absDiff a b
          if d < threshold then true else inner (idx2 + 1)
        else
          false
      if inner 0 then true else outer (idx + 1)
    else
      false
  outer 0
end RPOrig

namespace RPRef

private def has_close_elements__rp_helper_45724460 (numbers : List Float) (threshold : Float) (h_precond : has_close_elements_precond (numbers) (threshold)) : Bool :=
  let len := numbers.length
  let rec outer (idx : Nat) : Bool :=
    if idx < len then
      let rec inner (idx2 : Nat) : Bool :=
        if idx2 < idx then
          let a := numbers.getD idx2 0.0
          let b := numbers.getD idx 0.0
          let d := absDiff a b
          if d < threshold then true else inner (idx2 + 1)
        else
          false
      if inner 0 then true else outer (idx + 1)
    else
      false
  outer 0

def has_close_elements (numbers : List Float) (threshold : Float) (h_precond : has_close_elements_precond (numbers) (threshold)) : Bool :=
  has_close_elements__rp_helper_45724460 numbers threshold h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (numbers : List Float) (threshold : Float) (h_precond : has_close_elements_precond (numbers) (threshold)) :
    RPOrig.has_close_elements numbers threshold h_precond = RPRef.has_close_elements numbers threshold h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (numbers : List Float) (threshold : Float) (h_precond : has_close_elements_precond (numbers) (threshold)) :
    RPOrig.has_close_elements numbers threshold h_precond = RPRef.has_close_elements numbers threshold h_precond := rfl

theorem rp_equiv_delta_rfl (numbers : List Float) (threshold : Float) (h_precond : has_close_elements_precond (numbers) (threshold)) :
    RPOrig.has_close_elements numbers threshold h_precond = RPRef.has_close_elements numbers threshold h_precond := by
  first
    | (delta RPOrig.has_close_elements RPRef.has_close_elements RPRef.has_close_elements__rp_helper_45724460 RPOrig.has_close_elements.outer RPOrig.has_close_elements.outer.inner RPRef.has_close_elements__rp_helper_45724460.outer RPRef.has_close_elements__rp_helper_45724460.outer.inner; rfl)
    | (delta RPOrig.has_close_elements RPRef.has_close_elements RPRef.has_close_elements__rp_helper_45724460 RPOrig.has_close_elements.outer RPOrig.has_close_elements.outer.inner RPRef.has_close_elements__rp_helper_45724460.outer RPRef.has_close_elements__rp_helper_45724460.outer.inner RPOrig.has_close_elements._unary RPOrig.has_close_elements.outer._unary RPOrig.has_close_elements.outer.inner._unary RPRef.has_close_elements__rp_helper_45724460.outer._unary RPRef.has_close_elements__rp_helper_45724460.outer.inner._unary; rfl)
    | (set_option smartUnfolding false in rfl)

theorem rp_equiv_simp_only (numbers : List Float) (threshold : Float) (h_precond : has_close_elements_precond (numbers) (threshold)) :
    RPOrig.has_close_elements numbers threshold h_precond = RPRef.has_close_elements numbers threshold h_precond := by
  (simp only [RPOrig.has_close_elements, RPRef.has_close_elements, RPRef.has_close_elements__rp_helper_45724460]) <;> (first | rfl | (delta RPOrig.has_close_elements RPRef.has_close_elements RPRef.has_close_elements__rp_helper_45724460 RPOrig.has_close_elements.outer RPOrig.has_close_elements.outer.inner RPRef.has_close_elements__rp_helper_45724460.outer RPRef.has_close_elements__rp_helper_45724460.outer.inner; rfl) | (delta RPOrig.has_close_elements RPRef.has_close_elements RPRef.has_close_elements__rp_helper_45724460 RPOrig.has_close_elements.outer RPOrig.has_close_elements.outer.inner RPRef.has_close_elements__rp_helper_45724460.outer RPRef.has_close_elements__rp_helper_45724460.outer.inner RPOrig.has_close_elements._unary RPOrig.has_close_elements.outer._unary RPOrig.has_close_elements.outer.inner._unary RPRef.has_close_elements__rp_helper_45724460.outer._unary RPRef.has_close_elements__rp_helper_45724460.outer.inner._unary; rfl) | (set_option smartUnfolding false in rfl))

theorem rp_equiv_simp (numbers : List Float) (threshold : Float) (h_precond : has_close_elements_precond (numbers) (threshold)) :
    RPOrig.has_close_elements numbers threshold h_precond = RPRef.has_close_elements numbers threshold h_precond := by
  (simp [RPOrig.has_close_elements, RPRef.has_close_elements, RPRef.has_close_elements__rp_helper_45724460]) <;> (first | rfl | (delta RPOrig.has_close_elements RPRef.has_close_elements RPRef.has_close_elements__rp_helper_45724460 RPOrig.has_close_elements.outer RPOrig.has_close_elements.outer.inner RPRef.has_close_elements__rp_helper_45724460.outer RPRef.has_close_elements__rp_helper_45724460.outer.inner; rfl) | (delta RPOrig.has_close_elements RPRef.has_close_elements RPRef.has_close_elements__rp_helper_45724460 RPOrig.has_close_elements.outer RPOrig.has_close_elements.outer.inner RPRef.has_close_elements__rp_helper_45724460.outer RPRef.has_close_elements__rp_helper_45724460.outer.inner RPOrig.has_close_elements._unary RPOrig.has_close_elements.outer._unary RPOrig.has_close_elements.outer.inner._unary RPRef.has_close_elements__rp_helper_45724460.outer._unary RPRef.has_close_elements__rp_helper_45724460.outer.inner._unary; rfl) | (set_option smartUnfolding false in rfl))
