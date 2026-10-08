-- !benchmark @start import type=solution
import Mathlib
import Aesop
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def Triple_precond (x : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

private def Triple__rp_branch_9f218861 (x : Int) (h_precond : Triple_precond (x)) : Int :=
  let y := 2 * x
  x + y
-- !benchmark @end code_aux


def Triple (x : Int) (h_precond : Triple_precond (x)) : Int :=
  -- !benchmark @start code
  if x = 0 then 0 else
    Triple__rp_branch_9f218861 x h_precond
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def Triple_postcond (x : Int) (result: Int) (h_precond : Triple_precond (x)) :=
  -- !benchmark @start postcond
  result / 3 = x ∧ result / 3 * 3 = result
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem Triple_spec_satisfied (x: Int) (h_precond : Triple_precond (x)) :
    Triple_postcond (x) (Triple (x) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_main : Triple (x) h_precond / 3 = x := by
    have h₁ : Triple (x) h_precond = if x = 0 then 0 else x + 2 * x := by
      rfl
    rw [h₁]
    split_ifs <;> simp_all [Triple, Triple_precond, Int.mul_emod, Int.add_emod]
    <;>
      (try { omega }) <;>
      (try {
        ring_nf
        <;>
        omega
      }) <;>
      (try {
        have h₂ : x ≠ 0 := by
          intro h
          simp_all
        omega
      })
    <;>
    (try {
      simp_all [Int.mul_emod, Int.add_emod]
      <;>
      omega
    })
    <;>
    (try {
      ring_nf at * <;>
      omega
    })
    <;>
    (try {
      cases x <;> simp_all [Int.mul_emod, Int.add_emod]
      <;>
      omega
    })
    <;>
    (try {
      norm_num at *
      <;>
      omega
    })

  have h_main₂ : (Triple (x) h_precond) / 3 * 3 = Triple (x) h_precond := by
    have h₁ : Triple (x) h_precond = if x = 0 then 0 else x + 2 * x := by
      rfl
    rw [h₁]
    split_ifs with h
    · -- Case x = 0
      simp_all [Triple, Triple_precond]
      <;> simp_all [Int.mul_emod, Int.add_emod]
      <;> omega
    · -- Case x ≠ 0
      have h₃ : x ≠ 0 := by simpa using h
      have h₄ : (x + 2 * x : ℤ) = 3 * x := by ring
      rw [h₄]
      have h₅ : (3 * x : ℤ) / 3 * 3 = 3 * x := by
        have h₅ : (3 * x : ℤ) % 3 = 0 := by
          simp [Int.mul_emod, Int.emod_emod]
          <;> omega
        have h₆ : (3 * x : ℤ) / 3 * 3 = 3 * x := by
          omega
        exact h₆
      omega

  constructor
  · -- Prove the first postcondition: (result / 3 = x)
    exact h_main
  · -- Prove the second postcondition: (result / 3 * 3 = result)
    simpa [Triple_postcond] using h_main₂
  -- !benchmark @end proof
