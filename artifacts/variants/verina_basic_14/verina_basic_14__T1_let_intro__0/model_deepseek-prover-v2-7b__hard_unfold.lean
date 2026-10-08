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
  unfold containsZ containsZ_postcond
  have h : containsZ_postcond s (containsZ s h_precond) h_precond := by
    simp [containsZ_postcond, List.mem_cons, List.any_cons, containsZ, containsZ_precond]
    <;>
    (try simp_all [containsZ_precond]) <;>
    (try simp_all [containsZ]) <;>
    (try aesop) <;>
    (try
      {
        by_cases h₀ : s.toList.any fun c => c = 'z' ∨ c = 'Z' <;>
        by_cases h₁ : ∃ x, x ∈ s.toList ∧ (x = 'z' ∨ x = 'Z') <;>
        simp_all [List.any_iff_exists] <;>
        aesop
      }) <;>
    (try
      {
        aesop
      }) <;>
    (try
      {
        simp_all [List.any_iff_exists]
        <;>
        tauto
      })
  exact h
  -- !benchmark @end proof
