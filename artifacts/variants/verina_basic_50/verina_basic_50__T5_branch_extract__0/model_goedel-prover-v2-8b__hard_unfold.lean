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

private def Abs__rp_branch_c6672445 (x : Int) (h_precond : Abs_precond (x)) : Int :=
  x
-- !benchmark @end code_aux


def Abs (x : Int) (h_precond : Abs_precond (x)) : Int :=
  -- !benchmark @start code
  if x < 0 then -x else
    Abs__rp_branch_c6672445 x h_precond
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
  unfold Abs Abs_postcond
  have h_main : Abs_postcond x (Abs (x) h_precond) h_precond := by
    simp [Abs_precond, Abs, abs_of_nonneg, abs_of_nonpos, Int.ofNat_eq_coe]
    <;>
    (try
      {
        split_ifs <;> simp_all (config := {decide := true})
        <;>
        (try omega) <;>
        (try
          {
            cases' le_or_lt 0 x with hx hx <;> simp_all [abs_of_nonneg, abs_of_neg] <;> omega
          })
      }) <;>
    (try
      {
        constructor <;> intro h <;>
        (try omega) <;>
        (try
          {
            cases' le_or_lt 0 x with hx hx <;> simp_all [abs_of_nonneg, abs_of_neg] <;> omega
          }) <;>
        (try
          {
            omega
          })
      }) <;>
    (try
      {
        cases' le_or_lt 0 x with hx hx <;> simp_all [abs_of_nonneg, abs_of_neg] <;> omega
      }) <;>
    (try
      {
        omega
      })
    <;>
    (try
      {
        aesop
      })
    <;>
    (try
      {
        linarith
      })
    <;>
    (try
      {
        omega
      })
  exact h_main
  -- !benchmark @end proof
