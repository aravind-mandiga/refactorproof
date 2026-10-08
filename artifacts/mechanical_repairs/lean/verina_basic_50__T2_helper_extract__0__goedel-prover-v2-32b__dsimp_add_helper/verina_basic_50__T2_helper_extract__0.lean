-- !benchmark @start import type=solution
import Mathlib
import Aesop
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def Abs_precond (x : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

private def Abs__rp_helper_4386b369 (x : Int) (h_precond : Abs_precond (x)) : Int :=
  if x < 0 then -x else x
-- !benchmark @end code_aux


def Abs (x : Int) (h_precond : Abs_precond (x)) : Int :=
  -- !benchmark @start code
  Abs__rp_helper_4386b369 x h_precond
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def Abs_postcond (x : Int) (result: Int) (h_precond : Abs_precond (x)) :=
  -- !benchmark @start postcond
  (x ≥ 0 → x = result) ∧ (x < 0 → x + result = 0)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem Abs_spec_satisfied (x: Int) (h_precond : Abs_precond (x)) :
    Abs_postcond (x) (Abs (x) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_main : (x ≥ 0 → x = Abs (x) h_precond) ∧ (x < 0 → x + Abs (x) h_precond = 0) := by
    constructor
    · -- Prove x ≥ 0 → x = Abs (x) h_precond
      intro hx
      have h₁ : Abs (x) h_precond = x := by
        dsimp [Abs, Abs__rp_helper_4386b369]
        split_ifs <;>
        (try { contradiction }) <;>
        (try { linarith }) <;>
        (try { simp_all [Abs_precond] }) <;>
        (try { omega })
        <;>
        simp_all [Abs_precond]
        <;>
        linarith
      rw [h₁]
    · -- Prove x < 0 → x + Abs (x) h_precond = 0
      intro hx
      have h₁ : Abs (x) h_precond = -x := by
        dsimp [Abs]
        split_ifs <;>
        (try { contradiction }) <;>
        (try { linarith }) <;>
        (try { simp_all [Abs_precond] }) <;>
        (try { omega })
        <;>
        simp_all [Abs_precond]
        <;>
        linarith
      rw [h₁]
      have h₂ : x + (-x) = 0 := by ring
      exact h₂
  -- Use the main result to conclude the proof
  simpa [Abs_postcond] using h_main
  -- !benchmark @end proof
