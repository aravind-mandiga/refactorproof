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
  have h_main : (x ≥ 0 → x = (if x < 0 then -x else x)) ∧ (x < 0 → x + (if x < 0 then -x else x) = 0) := by
    constructor
    · -- Prove the first part: x ≥ 0 → x = (if x < 0 then -x else x)
      intro hx
      split_ifs <;>
      (try { contradiction }) <;>
      (try { linarith }) <;>
      (try { simp_all }) <;>
      (try { omega })
      <;>
      (try {
        -- In the case x < 0, we have a contradiction with hx: x ≥ 0
        linarith
      })
    · -- Prove the second part: x < 0 → x + (if x < 0 then -x else x) = 0
      intro hx
      split_ifs <;>
      (try { contradiction }) <;>
      (try { linarith }) <;>
      (try { simp_all }) <;>
      (try { omega })
      <;>
      (try {
        -- In the case x ≥ 0, we have a contradiction with hx: x < 0
        linarith
      })
      <;>
      (try {
        -- In the case x < 0, we have x + (-x) = 0
        have h₁ : x + -x = 0 := by
          ring
        linarith
      })

  -- Use h_main to prove the original statement
  have h₁ : Abs_postcond x (Abs x h_precond) h_precond := by
    simp only [Abs, Abs_postcond] at h_main ⊢
    <;>
    (try simp_all) <;>
    (try tauto) <;>
    (try {
      cases' le_or_lt 0 x with hx hx <;>
      simp_all [hx] <;>
      (try { omega }) <;>
      (try { linarith }) <;>
      (try { ring_nf at * <;> omega })
    }) <;>
    (try {
      tauto
    })
    <;>
    (try {
      aesop
    })

  exact h₁
  -- !benchmark @end proof
