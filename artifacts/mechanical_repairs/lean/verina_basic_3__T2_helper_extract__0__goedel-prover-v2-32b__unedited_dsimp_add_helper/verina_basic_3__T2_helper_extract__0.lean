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

private def isDivisibleBy11__rp_helper_c39b37ae (n : Int) (h_precond : isDivisibleBy11_precond (n)) : Bool :=
  n % 11 == 0
-- !benchmark @end code_aux


def isDivisibleBy11 (n : Int) (h_precond : isDivisibleBy11_precond (n)) : Bool :=
  -- !benchmark @start code
  isDivisibleBy11__rp_helper_c39b37ae n h_precond
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
  have h_main : (if n % 11 == 0 then (∃ k : Int, n = 11 * k) else (∀ k : Int, ¬ n = 11 * k)) := by
    split_ifs with h
    · -- Case: n % 11 == 0
      have h₁ : ∃ k : Int, n = 11 * k := by
        have h₂ : (11 : Int) ∣ n := by
          -- Since n % 11 == 0, 11 divides n
          have h₃ : n % 11 = 0 := by simpa using h
          exact Int.dvd_of_emod_eq_zero h₃
        -- There exists an integer k such that n = 11 * k
        obtain ⟨k, hk⟩ := h₂
        exact ⟨k, by linarith⟩
      exact h₁
    · -- Case: n % 11 ≠ 0
      have h₁ : ∀ k : Int, ¬ n = 11 * k := by
        intro k hk
        have h₂ : n % 11 = 0 := by
          have h₃ : n = 11 * k := hk
          have h₄ : (11 * k : Int) % 11 = 0 := by
            -- (11 * k) % 11 = 0 for any integer k
            norm_num [Int.mul_emod, Int.emod_emod]
          rw [h₃]
          exact h₄
        -- This contradicts the assumption that n % 11 ≠ 0
        have h₃ : ¬(n % 11 == 0) := by simpa using h
        have h₄ : n % 11 == 0 := by
          simpa [h₂] using h₃
        contradiction
      exact h₁

  dsimp [isDivisibleBy11_postcond, isDivisibleBy11] at *
  split_ifs at h_main <;> simp_all (config := {decide := true})
  <;>
  (try { contradiction }) <;>
  (try {
    intro k hk
    have h₁ := h_main
    exfalso
    apply h₁
    <;> linarith
  }) <;>
  (try {
    obtain ⟨k, hk⟩ := h_main
    exact ⟨k, by linarith⟩
  })
  -- !benchmark @end proof
