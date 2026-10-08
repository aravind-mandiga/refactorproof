-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def singleDigitPrimeFactor_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def singleDigitPrimeFactor (n : Nat) (h_precond : singleDigitPrimeFactor_precond (n)) : Nat :=
  -- !benchmark @start code
  let __rp_tmp_d7e12052 : Nat :=
    if n == 0 then 0
    else if n % 2 == 0 then 2
    else if n % 3 == 0 then 3
    else if n % 5 == 0 then 5
    else if n % 7 == 0 then 7
    else 0
  __rp_tmp_d7e12052
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def singleDigitPrimeFactor_postcond (n : Nat) (result: Nat) (h_precond : singleDigitPrimeFactor_precond (n)) : Prop :=
  -- !benchmark @start postcond
  result ∈ [0, 2, 3, 5, 7] ∧
  (result = 0 → (n = 0 ∨ [2, 3, 5, 7].all (n % · ≠ 0))) ∧
  (result ≠ 0 → n ≠ 0 ∧ n % result == 0 ∧ (List.range result).all (fun x => x ∈ [2, 3, 5, 7] → n % x ≠ 0))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem singleDigitPrimeFactor_spec_satisfied (n: Nat) (h_precond : singleDigitPrimeFactor_precond (n)) :
    singleDigitPrimeFactor_postcond (n) (singleDigitPrimeFactor (n) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_main : singleDigitPrimeFactor_postcond (n) (singleDigitPrimeFactor (n) h_precond) h_precond := by
    have h₁ : singleDigitPrimeFactor (n) h_precond ∈ ([0, 2, 3, 5, 7] : List Nat) := by
      by_cases hn : n = 0
      · -- Case n = 0
        rw [hn]
        simp [singleDigitPrimeFactor]
        <;> aesop
      · -- Case n ≠ 0
        have h₂ : n ≠ 0 := hn
        have h₃ : singleDigitPrimeFactor (n) h_precond = if n % 2 = 0 then 2 else if n % 3 = 0 then 3 else if n % 5 = 0 then 5 else if n % 7 = 0 then 7 else 0 := by
          simp [singleDigitPrimeFactor, h₂, Nat.mod_eq_of_lt]
          <;> aesop
        rw [h₃]
        split_ifs <;> simp_all (config := {decide := true})
        <;> aesop

    have h₂ : (singleDigitPrimeFactor (n) h_precond = 0 → (n = 0 ∨ [2, 3, 5, 7].all (n % · ≠ 0))) ∧ (singleDigitPrimeFactor (n) h_precond ≠ 0 → n ≠ 0 ∧ n % singleDigitPrimeFactor (n) h_precond = 0 ∧ (List.range (singleDigitPrimeFactor (n) h_precond)).all (fun x => x ∈ ([2, 3, 5, 7] : List Nat) → n % x ≠ 0)) := by
      by_cases hn : n = 0
      · -- Case n = 0
        have h₃ : singleDigitPrimeFactor (n) h_precond = 0 := by
          simp [singleDigitPrimeFactor, hn]
          <;> aesop
        constructor
        · -- Prove the first part of the conjunction
          intro h₄
          simp_all
        · -- Prove the second part of the conjunction
          intro h₄
          simp_all
          <;> aesop
      · -- Case n ≠ 0
        have h₃ : n ≠ 0 := hn
        have h₄ : singleDigitPrimeFactor (n) h_precond = if n % 2 = 0 then 2 else if n % 3 = 0 then 3 else if n % 5 = 0 then 5 else if n % 7 = 0 then 7 else 0 := by
          simp [singleDigitPrimeFactor, h₃, Nat.mod_eq_of_lt]
          <;> aesop
        constructor
        · -- Prove the first part of the conjunction
          intro h₅
          have h₆ : singleDigitPrimeFactor (n) h_precond = 0 := h₅
          have h₇ : ¬n % 2 = 0 := by
            by_contra h₇
            have h₈ : n % 2 = 0 := h₇
            rw [h₄] at h₆
            split_ifs at h₆ <;> simp_all (config := {decide := true})
            <;> omega
          have h₈ : ¬n % 3 = 0 := by
            by_contra h₈
            have h₉ : n % 3 = 0 := h₈
            rw [h₄] at h₆
            split_ifs at h₆ <;> simp_all (config := {decide := true})
            <;> omega
          have h₉ : ¬n % 5 = 0 := by
            by_contra h₉
            have h₁₀ : n % 5 = 0 := h₉
            rw [h₄] at h₆
            split_ifs at h₆ <;> simp_all (config := {decide := true})
            <;> omega
          have h₁₀ : ¬n % 7 = 0 := by
            by_contra h₁₀
            have h₁₁ : n % 7 = 0 := h₁₀
            rw [h₄] at h₆
            split_ifs at h₆ <;> simp_all (config := {decide := true})
            <;> omega
          have h₁₁ : [2, 3, 5, 7].all (n % · ≠ 0) := by
            simp [List.all_cons, List.all_nil]
            <;> simp_all [Nat.mod_eq_of_lt]
            <;> omega
          exact Or.inr h₁₁
        · -- Prove the second part of the conjunction
          intro h₅
          have h₆ : singleDigitPrimeFactor (n) h_precond ≠ 0 := h₅
          have h₇ : singleDigitPrimeFactor (n) h_precond = if n % 2 = 0 then 2 else if n % 3 = 0 then 3 else if n % 5 = 0 then 5 else if n % 7 = 0 then 7 else 0 := by
            simp [singleDigitPrimeFactor, h₃, Nat.mod_eq_of_lt]
            <;> aesop
          have h₈ : n % singleDigitPrimeFactor (n) h_precond = 0 := by
            rw [h₇]
            split_ifs with h₈ h₉ h₁₀ h₁₁
            · -- Case n % 2 = 0
              omega
            · -- Case n % 3 = 0
              omega
            · -- Case n % 5 = 0
              omega
            · -- Case n % 7 = 0
              omega
            · -- Case none of the above
              exfalso
              simp_all (config := {decide := true})
          have h₉ : n ≠ 0 := by
            intro h₉
            simp_all
          have h₁₀ : (List.range (singleDigitPrimeFactor (n) h_precond)).all (fun x => x ∈ ([2, 3, 5, 7] : List Nat) → n % x ≠ 0) := by
            rw [h₇]
            split_ifs with h₁₀ h₁₁ h₁₂ h₁₃
            · -- Case n % 2 = 0
              simp_all [List.range_succ, List.all_cons, List.all_nil]
              <;> norm_num
              <;>
                (try omega) <;>
                (try
                  {
                    intros x hx
                    simp_all (config := {decide := true})
                    <;> omega
                  })
            · -- Case n % 3 = 0
              simp_all [List.range_succ, List.all_cons, List.all_nil]
              <;> norm_num
              <;>
                (try omega) <;>
                (try
                  {
                    intros x hx
                    simp_all (config := {decide := true})
                    <;> omega
                  })
            · -- Case n % 5 = 0
              simp_all [List.range_succ, List.all_cons, List.all_nil]
              <;> norm_num
              <;>
                (try omega) <;>
                (try
                  {
                    intros x hx
                    simp_all (config := {decide := true})
                    <;> omega
                  })
            · -- Case n % 7 = 0
              simp_all [List.range_succ, List.all_cons, List.all_nil]
              <;> norm_num
              <;>
                (try omega) <;>
                (try
                  {
                    intros x hx
                    simp_all (config := {decide := true})
                    <;> omega
                  })
            · -- Case none of the above
              exfalso
              simp_all (config := {decide := true})
          exact ⟨h₉, h₈, h₁₀⟩

    have h₃ : singleDigitPrimeFactor_postcond (n) (singleDigitPrimeFactor (n) h_precond) h_precond := by
      simp_all [singleDigitPrimeFactor_postcond]
      <;> aesop
    exact h₃
  exact h_main
  -- !benchmark @end proof


