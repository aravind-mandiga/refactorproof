-- !benchmark @start import type=solution
import Mathlib
import Aesop
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def ComputeIsEven_precond (x : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def ComputeIsEven (x : Int) (h_precond : ComputeIsEven_precond (x)) : Bool :=
  -- !benchmark @start code
  let __rp_tmp_6cb292eb : Bool :=
    if x % 2 = 0 then true else false
  __rp_tmp_6cb292eb
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def ComputeIsEven_postcond (x : Int) (result: Bool) (h_precond : ComputeIsEven_precond (x)) :=
  -- !benchmark @start postcond
  result = true ↔ ∃ k : Int, x = 2 * k
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem ComputeIsEven_spec_satisfied (x: Int) (h_precond : ComputeIsEven_precond (x)) :
    ComputeIsEven_postcond (x) (ComputeIsEven (x) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_main : ComputeIsEven_postcond x (ComputeIsEven x h_precond) h_precond := by
    simp only [ComputeIsEven_precond, ComputeIsEven, ComputeIsEven_postcond]
    split_ifs <;> simp_all (config := {decide := true})
    <;>
    (try
      {
        -- Prove the forward direction: if x % 2 = 0, then there exists k such that x = 2 * k
        use x / 2
        omega
      }) <;>
    (try
      {
        -- Prove the backward direction: if there exists k such that x = 2 * k, then x % 2 = 0
        have h₁ : x % 2 = 0 := by
          -- Use the fact that x = 2 * k to show x % 2 = 0
          omega
        omega
      }) <;>
    (try
      {
        -- Handle the case when x % 2 = 1
        omega
      }) <;>
    (try
      {
        -- Handle the case when x % 2 = 1
        omega
      })
  exact h_main
  -- !benchmark @end proof
