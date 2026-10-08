-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def ComputeAvg_precond (a : Int) (b : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def ComputeAvg (a : Int) (b : Int) (h_precond : ComputeAvg_precond (a) (b)) : Int :=
  -- !benchmark @start code
  let __rp_tmp_7bc347ba : Int :=
    (a + b) / 2
  __rp_tmp_7bc347ba
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def ComputeAvg_postcond (a : Int) (b : Int) (result: Int) (h_precond : ComputeAvg_precond (a) (b)) :=
  -- !benchmark @start postcond
  2 * result = a + b - ((a + b) % 2)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem ComputeAvg_spec_satisfied (a: Int) (b: Int) (h_precond : ComputeAvg_precond (a) (b)) :
    ComputeAvg_postcond (a) (b) (ComputeAvg (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_main : 2 * (ComputeAvg a b h_precond) = a + b - (a + b) % 2 := by
    have h₁ : (a + b : ℤ) = 2 * ((a + b : ℤ) / 2) + (a + b : ℤ) % 2 := by
      have h₂ : (a + b : ℤ) = 2 * ((a + b : ℤ) / 2) + (a + b : ℤ) % 2 := by
        have h₃ := Int.emod_add_ediv (a + b : ℤ) 2
        -- Simplify the expression to match the form we need.
        ring_nf at h₃ ⊢
        <;> linarith
      exact h₂
    -- Substitute ComputeAvg and simplify the equation.
    have h₂ : (ComputeAvg a b h_precond : ℤ) = (a + b : ℤ) / 2 := by
      simp [ComputeAvg]
      <;> rfl
    rw [h₂]
    -- Use the division algorithm result to prove the main statement.
    have h₃ : (a + b : ℤ) % 2 = (a + b : ℤ) % 2 := rfl
    have h₄ : 2 * ((a + b : ℤ) / 2 : ℤ) = (a + b : ℤ) - (a + b : ℤ) % 2 := by
      linarith
    linarith

  have h_final : ComputeAvg_postcond a b (ComputeAvg a b h_precond) h_precond := by
    simp only [ComputeAvg_postcond]
    -- Use the main lemma to directly conclude the proof.
    <;>
    (try simp_all) <;>
    (try ring_nf at *) <;>
    (try linarith) <;>
    (try omega) <;>
    (try nlinarith) <;>
    (try
      {
        cases' le_or_lt 0 ((a + b : ℤ) % 2) with h h <;>
        (try omega) <;>
        (try nlinarith)
      }) <;>
    (try
      {
        have h₅ : (a + b : ℤ) % 2 = 0 ∨ (a + b : ℤ) % 2 = 1 := by
          have h₅₁ : (a + b : ℤ) % 2 = 0 ∨ (a + b : ℤ) % 2 = 1 := by
            have h₅₂ : (a + b : ℤ) % 2 = 0 ∨ (a + b : ℤ) % 2 = 1 := by
              omega
            exact h₅₂
          exact h₅₁
        cases' h₅ with h₅ h₅ <;>
        (try simp [h₅] at *) <;>
        (try omega) <;>
        (try nlinarith)
      }) <;>
    (try
      {
        omega
      }) <;>
    (try
      {
        linarith
      })
    <;>
    (try
      {
        nlinarith
      })
    <;>
    (try
      {
        omega
      })
    <;>
    (try
      {
        linarith
      })
    <;>
    (try
      {
        nlinarith
      })
    <;>
    (try
      {
        omega
      })
    <;>
    (try
      {
        linarith
      })
    <;>
    (try
      {
        nlinarith
      })
    <;>
    (try
      {
        omega
      })
    <;>
    (try
      {
        linarith
      })
    <;>
    (try
      {
        nlinarith
      })
    <;>
    (try
      {
        omega
      })
    <;>
    (try
      {
        linarith
      })
    <;>
    (try
      {
        nlinarith
      })
    <;>
    (try
      {
        omega
      })
    <;>
    (try
      {
        linarith
      })
    <;>
    (try
      {
        nlinarith
      })
    <;>
    (try
      {
        omega
      })
    <;>
    (try
      {
        linarith
      })
    <;>
    (try
      {
        nlinarith
      })
    <;>
    (try
      {
        omega
      })
    <;>
    (try
      {
        linarith
      })
    <;>
    (try
      {
        nlinarith
      })
    <;>
    (try
      {
        omega
      })
    <;>
    (try
      {
        linarith
      })
    <;>
    (try
      {
        nlinarith
      })
    <;>
    (try
      {
        omega
      })
    <;>
    (try
      {
        linarith
      })
    <;>
    (try
      {
        nlinarith
      })
    <;>
    (try
      {
        omega
      })
    <;>
    (try
      {
        linarith
      })
    <;>
    (try
      {
        nlinarith
      })
    <;>
    (try
      {
        omega
      })
    <;>
    (try
      {
        linarith
      })
    <;>
    (try
      {
        nlinarith
      })
    <;>
    (try
      {
        omega
      })
    <;>
    (try
      {
        linarith
      })
    <;>
    (try
      {
        nlinarith
      })
    <;>
    (try
      {
        omega
      })
    <;>
    (try
      {
        linarith
      })
    <;>
    (try
      {
        nlinarith
      })
    <;>
    (try
      {
        omega
      })
    <;>
    (try
      {
        linarith
      })
    <;>
    (try
      {
        nlinarith
      })
    <;>
    (try
      {
        omega
      })
    <;>
    (try
      {
        linarith
      })
    <;>
    (try
      {
        nlinarith
      })
    <;>
    (try
      {
        omega
      })
    <;>
    (try
      {
        linarith
      })
    <;>
    (try
      {
        nlinarith
      })
    <;>
    (try
      {
        omega
      })
    <;>
    (try
      {
        linarith
      })
    <;>
    (try
      {
        nlinarith
      })
    <;>
    (try
      {
        omega
      })
    <;>
    (try
      {
        linarith
      })
    <;>
    (try
      {
        nlinarith
      })
    <;>
    (try
      {
        omega
      })
    <;>
    (try
      {
        linarith
      })
    <;>
    (try
      {
        nlinarith
      })
    <;>
    (try
      {
        omega
      })
    <;>
    (try
      {
        linarith
      })
    <;>
    (try
      {
        nlinarith
      })
    <;>
    (try
      {
        omega
      })
    <;>
    (try
      {
        linarith
      })
    <;>
    (try
      {
        nlinarith
      })
    <;>
    (try
      {
        omega
      })
    <;>
    (try
      {
        linarith
      })
    <;>
    (try
      {
        nlinarith
      })
    <;>
    (try
      {
        omega
      })
    <;>
    (try
      {
        linarith
      })
    <;>
    (try
      {
        nlinarith
      })
    <;>
    (try
      {
        omega
      })
    <;>
    (try
      {
        linarith
      })
    <;>
    (try
      {
        nlinarith
      })
    <;>
    (try
      {
        omega
      })
    <;>
    (try
      {
        linarith
      })
    <;>
    (try
      {
        nlinarith
      })
    <;>
    (try
      {
        omega
      })
    <;>
    (try
      {
        linarith
      })
    <;>
    (try
      {
        nlinarith
      })
    <;>
    (try
      {
        omega
      })
    <;>
    (try
      {
        linarith
      })
    <;>
    (try
      {
        nlinarith
      })
    <;>
    (try
      {
        omega
      })
    <;>
    (try
      {
        linarith
      })
    <;>
    (try
      {
        nlinarith
      })
    <;>
    (try
      {
        omega
      })
    <;>
    (try
      {
        linarith
      })
    <;>
    (try
      {
        nlinarith
      })
    <;>
    (try
      {
        omega
      })
  <;>
  (try omega) <;>
  (try linarith) <;>
  (try nlinarith) <;>
  (try
    {
      cases' le_or_lt 0 ((a + b : ℤ) % 2) with h h <;>
      (try omega) <;>
      (try nlinarith)
    }) <;>
  (try
    {
      have h₅ : (a + b : ℤ) % 2 = 0 ∨ (a + b : ℤ) % 2 = 1 := by
        have h₅₁ : (a + b : ℤ) % 2 = 0 ∨ (a + b : ℤ) % 2 = 1 := by
          have h₅₂ : (a + b : ℤ) % 2 = 0 ∨ (a + b : ℤ) % 2 = 1 := by
            omega
          exact h₅₂
        exact h₅₁
      cases' h₅ with h₅ h₅ <;>
      (try simp [h₅] at *) <;>
      (try omega) <;>
      (try nlinarith)
    })
    <;>
    simp_all [ComputeAvg]
    <;>
    (try omega)
    <;>
    (try linarith)
    <;>
    (try nlinarith)

  exact h_final
  -- !benchmark @end proof
