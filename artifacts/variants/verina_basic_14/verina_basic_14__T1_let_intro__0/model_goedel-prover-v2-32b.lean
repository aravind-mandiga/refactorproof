-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def containsZ_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def containsZ (s : String) (h_precond : containsZ_precond (s)) : Bool :=
  -- !benchmark @start code
  let __rp_tmp_70a11263 : Bool :=
    s.toList.any fun c => c = 'z' || c = 'Z'
  __rp_tmp_70a11263
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def containsZ_postcond (s : String) (result: Bool) (h_precond : containsZ_precond (s)) :=
  -- !benchmark @start postcond
  let cs := s.toList
  (∃ x, x ∈ cs ∧ (x = 'z' ∨ x = 'Z')) ↔ result
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem containsZ_spec_satisfied (s: String) (h_precond : containsZ_precond (s)) :
    containsZ_postcond (s) (containsZ (s) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_main : (s.toList.any (fun c : Char => c = 'z' || c = 'Z') = true) ↔ (∃ x, x ∈ s.toList ∧ (x = 'z' ∨ x = 'Z')) := by
    constructor
    · -- Prove the forward direction: if any returns true, then there exists a 'z' or 'Z'
      intro h
      have h₁ : ∃ (x : Char), x ∈ s.toList ∧ (x = 'z' ∨ x = 'Z') := by
        -- Use the property of List.any to get the existence of an element satisfying the predicate
        have h₂ : s.toList.any (fun c : Char => c = 'z' || c = 'Z') = true := h
        have h₃ : ∃ (x : Char), x ∈ s.toList ∧ (x = 'z' || x = 'Z') = true := by
          -- Use the fact that List.any returns true to find an element
          have h₄ : s.toList.any (fun c : Char => c = 'z' || c = 'Z') = true := h₂
          -- Use the lemma List.any_eq_true to get the existence of an element
          have h₅ : ∃ (x : Char), x ∈ s.toList ∧ (x = 'z' || x = 'Z') = true := by
            -- Use the lemma List.any_eq_true to get the existence of an element
            simpa [List.any_eq_true] using h₄
          exact h₅
        -- Convert the existence of an element with (x = 'z' || x = 'Z') = true to (x = 'z' ∨ x = 'Z')
        obtain ⟨x, hx, hx'⟩ := h₃
        have h₆ : x = 'z' ∨ x = 'Z' := by
          -- Prove that (x = 'z' || x = 'Z') = true implies x = 'z' ∨ x = 'Z'
          have h₇ : (x = 'z' || x = 'Z') = true := hx'
          -- Consider the cases for x
          by_cases h₈ : x = 'z'
          · -- Case: x = 'z'
            exact Or.inl h₈
          · -- Case: x ≠ 'z'
            have h₉ : x = 'Z' := by
              -- Since x ≠ 'z', we need to check if x = 'Z'
              have h₁₀ : (x = 'z' || x = 'Z') = true := h₇
              have h₁₁ : x ≠ 'z' := h₈
              have h₁₂ : x = 'Z' := by
                -- Use the fact that (x = 'z' || x = 'Z') = true and x ≠ 'z' to deduce x = 'Z'
                simp [h₁₁, or_iff_not_imp_left] at h₁₀
                <;> simp_all [Bool.and_eq_true]
              exact h₁₂
            exact Or.inr h₉
        -- Combine the results to get the final existence statement
        exact ⟨x, hx, h₆⟩
      -- Convert the existence statement to the required form
      simpa using h₁
    · -- Prove the reverse direction: if there exists a 'z' or 'Z', then any returns true
      intro h
      have h₁ : s.toList.any (fun c : Char => c = 'z' || c = 'Z') = true := by
        -- Use the existence of 'z' or 'Z' to prove that any returns true
        obtain ⟨x, hx, hx'⟩ := h
        have h₂ : x ∈ s.toList := hx
        have h₃ : x = 'z' ∨ x = 'Z' := hx'
        have h₄ : (x = 'z' || x = 'Z') = true := by
          -- Prove that (x = 'z' || x = 'Z') = true given x = 'z' ∨ x = 'Z'
          cases h₃ with
          | inl h₃ =>
            -- Case: x = 'z'
            simp [h₃]
          | inr h₃ =>
            -- Case: x = 'Z'
            simp [h₃]
        -- Use the fact that there exists an element satisfying the predicate to prove that any returns true
        have h₅ : s.toList.any (fun c : Char => c = 'z' || c = 'Z') = true := by
          -- Use the lemma List.any_eq_true to prove that any returns true
          have h₆ : ∃ (x : Char), x ∈ s.toList ∧ (x = 'z' || x = 'Z') = true := ⟨x, h₂, h₄⟩
          simpa [List.any_eq_true] using h₆
        exact h₅
      exact h₁

  have h_final : containsZ_postcond (s) (containsZ (s) h_precond) h_precond := by
    dsimp [containsZ_postcond] at *
    have h₁ : containsZ s h_precond = s.toList.any (fun c : Char => c = 'z' || c = 'Z') := rfl
    rw [h₁]
    -- Use the previously established equivalence to conclude the proof
    <;> simp_all [h_main]
    <;> tauto

  exact h_final
  -- !benchmark @end proof
