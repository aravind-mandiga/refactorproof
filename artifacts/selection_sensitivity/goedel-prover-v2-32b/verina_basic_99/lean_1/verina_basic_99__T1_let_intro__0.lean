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

-- !benchmark @end code_aux


def Triple (x : Int) (h_precond : Triple_precond (x)) : Int :=
  -- !benchmark @start code
  let __rp_tmp_25d1f142 : Int :=
    if x < 18 then
      let a := 2 * x
      let b := 4 * x
      (a + b) / 2
    else
      let y := 2 * x
      x + y
  __rp_tmp_25d1f142
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
  have h_main : Triple (x) h_precond = 3 * x := by
    dsimp [Triple] at *
    split_ifs with h
    · -- Case: x < 18
      have h₁ : (2 * x + 4 * x : Int) / 2 = 3 * x := by
        have h₂ : (2 * x + 4 * x : Int) = 6 * x := by ring
        rw [h₂]
        have h₃ : (6 * x : Int) / 2 = 3 * x := by
          have h₄ : (6 * x : Int) % 2 = 0 := by
            have h₅ : (6 : Int) % 2 = 0 := by norm_num
            have h₆ : (x : Int) % 2 = 0 ∨ (x : Int) % 2 = 1 ∨ (x : Int) % 2 = -1 := by
              have : (x : Int) % 2 = 0 ∨ (x : Int) % 2 = 1 ∨ (x : Int) % 2 = -1 := by
                omega
              tauto
            rcases h₆ with (h₆ | h₆ | h₆) <;>
              (try omega) <;>
                (try {
                  simp [h₆, Int.mul_emod, Int.add_emod]
                  <;> norm_num <;> omega
                }) <;>
                  (try {
                    simp [h₆, Int.mul_emod, Int.add_emod]
                    <;> norm_num <;> omega
                  })
          -- Since 6 * x is even, we can divide by 2 exactly
          have h₇ : (6 * x : Int) / 2 * 2 = 6 * x := by
            have h₈ : (6 * x : Int) % 2 = 0 := h₄
            have h₉ : (6 * x : Int) / 2 * 2 = 6 * x := by
              have h₁₀ := Int.emod_add_ediv (6 * x : Int) 2
              omega
            exact h₉
          -- Simplify the division
          have h₈ : (6 * x : Int) / 2 = 3 * x := by
            have h₉ : (6 * x : Int) / 2 * 2 = 6 * x := h₇
            have h₁₀ : (6 * x : Int) / 2 = 3 * x := by
              ring_nf at h₉ ⊢
              <;> omega
            exact h₁₀
          exact h₈
        rw [h₃]
        <;> ring_nf
        <;> omega
      -- Simplify the expression using the above result
      dsimp at *
      <;> simp_all [add_assoc]
      <;> ring_nf at *
      <;> omega
    · -- Case: x ≥ 18
      -- Simplify the expression directly
      dsimp at *
      <;> ring_nf at *
      <;> omega

  have h_div : (3 * x : Int) / 3 = x := by
    have h₁ : (3 : Int) ≠ 0 := by norm_num
    have h₂ : (3 * x : Int) / 3 = x := by
      have h₃ : (3 * x : Int) / 3 = x := by
        -- Use the property of division and multiplication to simplify the expression
        apply Int.ediv_eq_of_eq_mul_right (by norm_num : (3 : Int) ≠ 0)
        <;> ring_nf
        <;> norm_num
        <;> linarith
      exact h₃
    exact h₂

  have h_mul : (3 * x : Int) / 3 * 3 = 3 * x := by
    have h₁ : (3 * x : Int) / 3 = x := h_div
    rw [h₁]
    <;> ring_nf
    <;> omega

  have h_final : Triple_postcond x (Triple x h_precond) h_precond := by
    have h₁ : Triple x h_precond = 3 * x := h_main
    have h₂ : (3 * x : Int) / 3 = x := h_div
    have h₃ : (3 * x : Int) / 3 * 3 = 3 * x := h_mul
    simp only [h₁, Triple_postcond] at *
    <;>
    (try norm_num at *) <;>
    (try simp_all [h₂, h₃]) <;>
    (try ring_nf at *) <;>
    (try norm_num) <;>
    (try omega)
    <;>
    (try
      {
        constructor <;>
        (try simp_all [h₂, h₃]) <;>
        (try ring_nf at *) <;>
        (try norm_num) <;>
        (try omega)
      })

  exact h_final
  -- !benchmark @end proof
