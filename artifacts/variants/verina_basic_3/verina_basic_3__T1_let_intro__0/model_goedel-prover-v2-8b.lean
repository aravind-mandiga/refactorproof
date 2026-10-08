-- !benchmark @start import type=solution
import Mathlib
import Aesop
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isDivisibleBy11_precond (n : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def isDivisibleBy11 (n : Int) (h_precond : isDivisibleBy11_precond (n)) : Bool :=
  -- !benchmark @start code
  let __rp_tmp_24877dad : Bool :=
    n % 11 == 0
  __rp_tmp_24877dad
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def isDivisibleBy11_postcond (n : Int) (result: Bool) (h_precond : isDivisibleBy11_precond (n)) :=
  -- !benchmark @start postcond
  (result → (∃ k : Int, n = 11 * k)) ∧ (¬ result → (∀ k : Int, ¬ n = 11 * k))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem isDivisibleBy11_spec_satisfied (n: Int) (h_precond : isDivisibleBy11_precond (n)) :
    isDivisibleBy11_postcond (n) (isDivisibleBy11 (n) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_main : isDivisibleBy11_postcond (n) (isDivisibleBy11 (n) h_precond) h_precond := by
    simp only [isDivisibleBy11_precond, isDivisibleBy11, isDivisibleBy11_postcond]
    <;>
    by_cases h : n % 11 = 0 <;>
    simp_all [Int.emod_eq_of_lt]
    <;>
    (try { omega }) <;>
    (try {
      -- For the case where n % 11 ≠ 0, we need to show that no k exists such that n = 11 * k
      -- Assume for contradiction that n = 11 * k
      intro k hk
      have h₁ := congr_arg (· % 11) hk
      simp at h₁
      <;>
      omega
    }) <;>
    (try {
      -- For the case where n % 11 = 0, we need to find a k such that n = 11 * k
      -- Take k = n / 11
      use n / 11
      have h₁ : n % 11 = 0 := by omega
      have h₂ : n = 11 * (n / 11) := by
        omega
      omega
    }) <;>
    (try {
      -- This is a placeholder for the actual contradiction proof
      exfalso
      omega
    })
  exact h_main
  -- !benchmark @end proof
