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
  have h_main : (isDivisibleBy11 (n) h_precond → (∃ k : Int, n = 11 * k)) ∧ (¬ isDivisibleBy11 (n) h_precond → (∀ k : Int, ¬ n = 11 * k)) := by
    have h₁ : (isDivisibleBy11 (n) h_precond = true) ↔ (n % 11 : Int) = 0 := by
      constructor
      · intro h
        -- Prove the forward direction: if isDivisibleBy11 (n) = true, then n % 11 = 0
        simp [isDivisibleBy11] at h
        <;>
        (try norm_num at h) <;>
        (try omega) <;>
        (try
          {
            -- Since n % 11 is an integer, we can directly use the equality
            have h₂ : (n % 11 : Int) = 0 := by
              norm_cast at h ⊢
              <;>
              simp_all [Int.emod_eq_of_lt]
              <;>
              omega
            exact h₂
          })
        <;>
        simp_all [Int.emod_eq_of_lt]
        <;>
        omega
      · intro h
        -- Prove the reverse direction: if n % 11 = 0, then isDivisibleBy11 (n) = true
        simp [isDivisibleBy11]
        <;>
        norm_cast at h ⊢ <;>
        simp_all [Int.emod_eq_of_lt]
        <;>
        omega

    have h₂ : (isDivisibleBy11 (n) h_precond = false) ↔ (n % 11 : Int) ≠ 0 := by
      constructor
      · intro h
        -- Prove the forward direction: if isDivisibleBy11 (n) = false, then n % 11 ≠ 0
        have h₃ : (isDivisibleBy11 (n) h_precond = true) ↔ (n % 11 : Int) = 0 := h₁
        have h₄ : ¬(isDivisibleBy11 (n) h_precond = true) := by
          intro h₄
          simp_all
        have h₅ : ¬((n % 11 : Int) = 0) := by
          intro h₅
          have h₆ : (isDivisibleBy11 (n) h_precond = true) := by
            have h₇ : (isDivisibleBy11 (n) h_precond = true) ↔ (n % 11 : Int) = 0 := h₁
            simp_all
          contradiction
        exact h₅
      · intro h
        -- Prove the reverse direction: if n % 11 ≠ 0, then isDivisibleBy11 (n) = false
        have h₃ : (isDivisibleBy11 (n) h_precond = true) ↔ (n % 11 : Int) = 0 := h₁
        have h₄ : ¬(isDivisibleBy11 (n) h_precond = true) := by
          intro h₄
          have h₅ : (n % 11 : Int) = 0 := by
            have h₆ : (isDivisibleBy11 (n) h_precond = true) ↔ (n % 11 : Int) = 0 := h₁
            simp_all
          contradiction
        have h₅ : isDivisibleBy11 (n) h_precond = false := by
          cases h₆ : isDivisibleBy11 (n) h_precond <;> simp_all (config := {decide := true})
        exact h₅

    constructor
    · -- Prove the forward direction: if isDivisibleBy11 (n) = true, then ∃ k : Int, n = 11 * k
      intro h
      have h₃ : (isDivisibleBy11 (n) h_precond = true) := by
        cases h₄ : isDivisibleBy11 (n) h_precond <;> simp_all (config := {decide := true})
      have h₄ : (n % 11 : Int) = 0 := by
        have h₅ : (isDivisibleBy11 (n) h_precond = true) ↔ (n % 11 : Int) = 0 := h₁
        simp_all
      -- Use the fact that n % 11 = 0 to find k such that n = 11 * k
      have h₅ : ∃ k : Int, n = 11 * k := by
        use n / 11
        have h₆ : n = 11 * (n / 11) + (n % 11) := by
          have h₇ := Int.emod_add_ediv n 11
          linarith
        rw [h₄] at h₆
        ring_nf at h₆ ⊢
        <;> linarith
      exact h₅
    · -- Prove the reverse direction: if isDivisibleBy11 (n) = false, then ∀ k : Int, ¬ n = 11 * k
      intro h
      have h₃ : (isDivisibleBy11 (n) h_precond = false) := by
        cases h₄ : isDivisibleBy11 (n) h_precond <;> simp_all (config := {decide := true})
      have h₄ : (n % 11 : Int) ≠ 0 := by
        have h₅ : (isDivisibleBy11 (n) h_precond = false) ↔ (n % 11 : Int) ≠ 0 := h₂
        simp_all
      -- Use the fact that n % 11 ≠ 0 to show that no k exists such that n = 11 * k
      intro k hk
      have h₅ : (n % 11 : Int) = 0 := by
        have h₆ : n = 11 * k := hk
        have h₇ : (n : Int) % 11 = (11 * k : Int) % 11 := by
          rw [h₆]
        have h₈ : (11 * k : Int) % 11 = 0 := by
          norm_num [Int.mul_emod]
        have h₉ : (n : Int) % 11 = 0 := by
          omega
        exact_mod_cast h₉
      contradiction

  have h_final : isDivisibleBy11_postcond (n) (isDivisibleBy11 (n) h_precond) h_precond := by
    simp only [isDivisibleBy11_postcond]
    exact h_main

  exact h_final
  -- !benchmark @end proof
