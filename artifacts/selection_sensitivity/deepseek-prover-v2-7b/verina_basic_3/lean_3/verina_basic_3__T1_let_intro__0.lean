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
    constructor
    · -- Prove the first implication: if `isDivisibleBy11 n h_precond` is true, then `n = 11 * k` for some integer `k`.
      intro h
      have h₁ : n % 11 = 0 := by
        -- Simplify the hypothesis `h` to get `n % 11 = 0`.
        simp_all [isDivisibleBy11, isDivisibleBy11_precond]
        <;>
        aesop
      -- Since `n % 11 = 0`, `n` is divisible by `11`.
      have h₂ : ∃ k : Int, n = 11 * k := by
        use n / 11
        have h₃ : n % 11 = 0 := h₁
        -- Use the fact that `n % 11 = 0` to show `n = 11 * (n / 11)`.
        have h₄ : n = 11 * (n / 11) := by
          have h₅ := Int.emod_add_ediv n 11
          omega
        linarith
      exact h₂
    · -- Prove the second implication: if `isDivisibleBy11 n h_precond` is false, then `n ≠ 11 * k` for any integer `k`.
      intro h
      intro k
      have h₁ : n % 11 ≠ 0 := by
        intro h₂
        have h₃ : isDivisibleBy11 (n) h_precond := by
          simp_all [isDivisibleBy11, isDivisibleBy11_precond]
          <;> aesop
        contradiction
      -- Assume for contradiction that `n = 11 * k` for some `k`.
      intro h₂
      have h₃ : n % 11 = 0 := by
        -- Use the assumption `n = 11 * k` to show `n % 11 = 0`.
        have h₄ : n = 11 * k := h₂
        rw [h₄]
        simp [Int.mul_emod, Int.emod_emod]
      contradiction

  exact h_main
  -- !benchmark @end proof
