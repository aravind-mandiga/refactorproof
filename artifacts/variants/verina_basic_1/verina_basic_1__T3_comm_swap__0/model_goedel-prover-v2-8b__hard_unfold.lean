-- !benchmark @start import type=solution
import Mathlib
import Aesop
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def hasOppositeSign_precond (a : Int) (b : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def hasOppositeSign (a : Int) (b : Int) (h_precond : hasOppositeSign_precond (a) (b)) : Bool :=
  -- !benchmark @start code
  b * a < 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def hasOppositeSign_postcond (a : Int) (b : Int) (result: Bool) (h_precond : hasOppositeSign_precond (a) (b)) :=
  -- !benchmark @start postcond
  (((a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0)) → result) ∧
  (¬((a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0)) → ¬result)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem hasOppositeSign_spec_satisfied (a: Int) (b: Int) (h_precond : hasOppositeSign_precond (a) (b)) :
    hasOppositeSign_postcond (a) (b) (hasOppositeSign (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold hasOppositeSign hasOppositeSign_postcond
  have h_main : hasOppositeSign_postcond (a) (b) (hasOppositeSign (a) (b) h_precond) h_precond := by
    dsimp only [hasOppositeSign, hasOppositeSign_postcond, hasOppositeSign_precond] at *
    <;>
    (try constructor) <;>
    (try simp_all) <;>
    (try
      {
        by_cases h₁ : a < 0 <;> by_cases h₂ : b < 0 <;> by_cases h₃ : a > 0 <;> by_cases h₄ : b > 0 <;>
          simp_all [mul_comm, mul_assoc, mul_left_comm, Int.mul_emod, Int.add_emod, Int.sub_emod]
        <;>
          (try omega) <;>
          (try
            {
              nlinarith
            }) <;>
          (try
            {
              aesop
            })
      }) <;>
    (try
      {
        by_cases h₁ : a < 0 <;> by_cases h₂ : b < 0 <;> by_cases h₃ : a > 0 <;> by_cases h₄ : b > 0 <;>
          simp_all [mul_comm, mul_assoc, mul_left_comm, Int.mul_emod, Int.add_emod, Int.sub_emod]
        <;>
          (try omega) <;>
          (try
            {
              nlinarith
            }) <;>
          (try
            {
              aesop
            })
      }) <;>
    (try
      {
        aesop
      }) <;>
    (try
      {
        omega
      })
  exact h_main
  -- !benchmark @end proof
