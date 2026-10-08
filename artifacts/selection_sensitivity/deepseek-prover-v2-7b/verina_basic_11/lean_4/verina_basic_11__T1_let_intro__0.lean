-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def lastDigit_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def lastDigit (n : Nat) (h_precond : lastDigit_precond (n)) : Nat :=
  -- !benchmark @start code
  let __rp_tmp_c1b8a8ca : Nat :=
    n % 10
  __rp_tmp_c1b8a8ca
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def lastDigit_postcond (n : Nat) (result: Nat) (h_precond : lastDigit_precond (n)) :=
  -- !benchmark @start postcond
  (0 ≤ result ∧ result < 10) ∧
  (n % 10 - result = 0 ∧ result - n % 10 = 0)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem lastDigit_spec_satisfied (n: Nat) (h_precond : lastDigit_precond (n)) :
    lastDigit_postcond (n) (lastDigit (n) h_precond) h_precond := by
  -- !benchmark @start proof
  have h1 : 0 ≤ lastDigit (n) h_precond ∧ lastDigit (n) h_precond < 10 := by
    constructor
    · -- Prove that 0 ≤ n % 10
      simp [lastDigit, h_precond]
      <;> omega
    · -- Prove that n % 10 < 10
      simp [lastDigit, h_precond]
      <;> omega
  have h2 : (lastDigit (n) h_precond - lastDigit (n) h_precond = 0 ∧ lastDigit (n) h_precond - lastDigit (n) h_precond = 0) := by
    constructor <;> simp [lastDigit, h_precond]
    <;>
    (try omega) <;>
    (try ring_nf) <;>
    (try omega)
  exact ⟨h1, by simp_all [lastDigit_postcond, lastDigit]⟩
  -- !benchmark @end proof
