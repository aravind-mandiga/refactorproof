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

private def containsZ__rp_helper_6f400cbb (s : String) (h_precond : containsZ_precond (s)) : Bool :=
  s.toList.any fun c => c = 'z' || c = 'Z'
-- !benchmark @end code_aux


def containsZ (s : String) (h_precond : containsZ_precond (s)) : Bool :=
  -- !benchmark @start code
  containsZ__rp_helper_6f400cbb s h_precond
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
  have h_main : (∃ x, x ∈ s.toList ∧ (x = 'z' ∨ x = 'Z')) ↔ (s.toList.any fun c => c = 'z' || c = 'Z') := by
    constructor
    · -- Prove the forward direction: (∃ x, x ∈ s.toList ∧ (x = 'z' ∨ x = 'Z')) → (s.toList.any fun c => c = 'z' || c = 'Z')
      intro h
      -- Use the definition of `List.any` to show the equivalence
      have h₁ : s.toList.any (fun c => c = 'z' || c = 'Z') := by
        -- Use the fact that `List.any` is equivalent to the existential form
        simpa [List.any_cons, List.mem_cons, or_imp, or_assoc] using h
      exact h₁
    · -- Prove the backward direction: (s.toList.any fun c => c = 'z' || c = 'Z') → (∃ x, x ∈ s.toList ∧ (x = 'z' ∨ x = 'Z'))
      intro h
      -- Use the definition of `List.any` to show the equivalence
      have h₁ : ∃ x, x ∈ s.toList ∧ (x = 'z' ∨ x = 'Z') := by
        -- Use the fact that `List.any` is equivalent to the existential form
        simpa [List.any_cons, List.mem_cons, or_imp, or_assoc] using h
      exact h₁

  -- Use the main lemma to prove the final statement
  simp_all [containsZ_postcond, containsZ, containsZ__rp_helper_6f400cbb]
  <;>
  aesop
  -- !benchmark @end proof
