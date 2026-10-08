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
  have h2 : ∀ (a : Int), (2 * a) / 2 = a := by
    intro a
    have h : (2 : Int) * a / 2 = a := by
      have h₁ : (2 : Int) * a % 2 = 0 := by
        have h₂ : (2 : Int) * a % 2 = 0 := by
          norm_num [Int.mul_emod, Int.emod_emod]
        exact h₂
      have h₃ : (2 : Int) * a / 2 * 2 + (2 : Int) * a % 2 = (2 : Int) * a := by
        have h₄ := Int.ediv_add_emod ((2 : Int) * a) 2
        linarith
      have h₄ : (2 : Int) * a / 2 * 2 = (2 : Int) * a := by
        omega
      have h₅ : (2 : Int) * a / 2 = a := by
        linarith
      exact h₅
    exact h

  have h3 : ∀ (a : Int), (3 * a) / 3 = a := by
    intro a
    have h : (3 : Int) * a / 3 = a := by
      have h₁ : (3 : Int) * a % 3 = 0 := by
        have h₂ : (3 : Int) * a % 3 = 0 := by
          norm_num [Int.mul_emod, Int.emod_emod]
        exact h₂
      have h₃ : (3 : Int) * a / 3 * 3 + (3 : Int) * a % 3 = (3 : Int) * a := by
        have h₄ := Int.ediv_add_emod ((3 : Int) * a) 3
        linarith
      have h₄ : (3 : Int) * a / 3 * 3 = (3 : Int) * a := by
        omega
      have h₅ : (3 : Int) * a / 3 = a := by
        linarith
      exact h₅
    exact h

  have h_triple_eq : Triple x h_precond = 3 * x := by
    by_cases h : x < 18
    · -- Case: x < 18
      have h₁ : Triple x h_precond = ( (2 * x) + (4 * x) ) / 2 := by
        simp [Triple, h_precond, h]
        <;> norm_num
        <;> ring_nf
        <;> rfl
      rw [h₁]
      have h₂ : ((2 * x) + (4 * x) : Int) = 6 * x := by ring
      rw [h₂]
      have h₃ : (6 * x : Int) / 2 = 3 * x := by
        have h₄ : (6 * x : Int) / 2 = (2 * (3 * x)) / 2 := by ring_nf
        rw [h₄]
        have h₅ : (2 * (3 * x) : Int) / 2 = 3 * x := by
          have h₆ := h2 (3 * x)
          ring_nf at h₆ ⊢
          <;> linarith
        rw [h₅]
      rw [h₃]
    · -- Case: x ≥ 18
      have h₁ : Triple x h_precond = x + 2 * x := by
        simp [Triple, h_precond, h]
        <;> norm_num at h ⊢ <;>
        (try omega) <;>
        (try ring_nf) <;>
        (try simp_all) <;>
        (try norm_num) <;>
        (try linarith)
        <;>
        (try
          {
            split_ifs at * <;>
            norm_num at * <;>
            linarith
          })
        <;>
        (try omega)
      rw [h₁]
      <;> ring_nf
      <;> norm_num
      <;> linarith

  have h_div : (Triple x h_precond) / 3 = x := by
    rw [h_triple_eq]
    have h₁ : (3 * x : Int) / 3 = x := by
      have h₂ := h3 x
      ring_nf at h₂ ⊢
      <;> linarith
    exact h₁

  have h_mul : ( (Triple x h_precond) / 3 ) * 3 = Triple x h_precond := by
    have h₁ : (Triple x h_precond) / 3 = x := h_div
    rw [h₁]
    have h₂ : Triple x h_precond = 3 * x := h_triple_eq
    rw [h₂]
    <;> ring_nf
    <;> norm_num
    <;> linarith

  simp [Triple_postcond, h_precond] at *
  <;>
  (try constructor) <;>
  (try simp_all) <;>
  (try norm_num) <;>
  (try linarith)
  <;>
  (try ring_nf at *) <;>
  (try linarith)
  -- !benchmark @end proof
