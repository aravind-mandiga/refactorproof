-- !benchmark @start import type=solution

import Aesop
import Mathlib
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


-- !benchmark @start code_aux

private def SwapArithmetic__rp_helper_2265221a (X : Int) (Y : Int) (h_precond : SwapArithmetic_precond (X) (Y)) : (Int × Int) :=
  let x1 := X
  let y1 := Y
  let x2 := y1 - x1
  let y2 := y1 - x2
  let x3 := y2 + x2
  (x3, y2)
-- !benchmark @end code_aux


def SwapArithmetic (X : Int) (Y : Int) (h_precond : SwapArithmetic_precond (X) (Y)) : (Int × Int) :=
  -- !benchmark @start code
  SwapArithmetic__rp_helper_2265221a X Y h_precond
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def SwapArithmetic_postcond (X : Int) (Y : Int) (result: (Int × Int)) (h_precond : SwapArithmetic_precond (X) (Y)) :=
  -- !benchmark @start postcond
  result.1 = Y ∧ result.2 = X ∧
  (X ≠ Y → result.fst ≠ X ∧ result.snd ≠ Y)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem SwapArithmetic_spec_satisfied (X: Int) (Y: Int) (h_precond : SwapArithmetic_precond (X) (Y)) :
    SwapArithmetic_postcond (X) (Y) (SwapArithmetic (X) (Y) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_main : SwapArithmetic (X) (Y) h_precond = (Y, X) := by
    simp [SwapArithmetic, SwapArithmetic_precond]
    <;>
    (try cases X <;> cases Y <;> simp_all [Int.mul_emod, Int.add_emod, Int.sub_emod])
    <;>
    (try ring_nf)
    <;>
    (try aesop)
    <;>
    (try simp_all [Prod.mk.injEq])
    <;>
    (try omega)

  have h_final : SwapArithmetic_postcond (X) (Y) (SwapArithmetic (X) (Y) h_precond) h_precond := by
    rw [h_main]
    <;> simp [SwapArithmetic_postcond, SwapArithmetic_precond]
    <;>
    (try
      {
        aesop
      })
    <;>
    (try
      {
        intros h_neq
        simp_all [Prod.mk.inj_iff]
        <;> omega
      })
    <;>
    (try
      {
        aesop
      })
    <;>
    (try
      {
        simp_all [Prod.mk.inj_iff]
        <;> omega
      })

  exact h_final
  -- !benchmark @end proof
