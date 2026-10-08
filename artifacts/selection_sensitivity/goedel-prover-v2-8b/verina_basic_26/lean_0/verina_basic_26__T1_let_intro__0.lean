-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isEven_precond (n : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def isEven (n : Int) (h_precond : isEven_precond (n)) : Bool :=
  -- !benchmark @start code
  let __rp_tmp_a74ca03e : Bool :=
    n % 2 == 0
  __rp_tmp_a74ca03e
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def isEven_postcond (n : Int) (result: Bool) (h_precond : isEven_precond (n)) :=
  -- !benchmark @start postcond
  (result → n % 2 = 0) ∧ (¬ result → n % 2 ≠ 0)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem isEven_spec_satisfied (n: Int) (h_precond : isEven_precond (n)) :
    isEven_postcond (n) (isEven (n) h_precond) h_precond := by
  -- !benchmark @start proof
  have h1 : isEven (n) h_precond → n % 2 = 0 := by
    intro h
    have h₂ : n % 2 == 0 := by
      simpa [isEven] using h
    have h₃ : n % 2 = 0 := by
      simp_all [isEven, isEven_precond]
      <;>
      (try omega) <;>
      (try norm_num at *) <;>
      (try omega) <;>
      (try ring_nf at *) <;>
      (try omega)
    exact h₃

  have h2 : ¬ isEven (n) h_precond → n % 2 ≠ 0 := by
    intro h
    have h₃ : n % 2 ≠ 0 := by
      by_contra h₄
      have h₅ : n % 2 = 0 := by simpa using h₄
      have h₆ : isEven (n) h_precond := by
        simp_all [isEven]
        <;>
        (try omega) <;>
        (try norm_num at *) <;>
        (try omega) <;>
        (try ring_nf at *) <;>
        (try omega)
      contradiction
    exact h₃

  have h_main : isEven_postcond (n) (isEven (n) h_precond) h_precond := by
    constructor
    · -- Prove the first part: if isEven (n) h_precond, then n % 2 = 0
      exact h1
    · -- Prove the second part: if ¬ isEven (n) h_precond, then n % 2 ≠ 0
      exact h2

  exact h_main
  -- !benchmark @end proof
