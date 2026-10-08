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
  unfold containsZ containsZ_postcond
  have h₁ : (s.toList.any (fun c => c = 'z' ∨ c = 'Z')) ↔ (s.toList.any (fun c => c = 'z' ∨ c = 'Z')) := by
    apply Iff.intro
    · intro h
      exact h
    · intro h
      exact h

  simp_all [containsZ_postcond, containsZ, List.any_cons, List.mem_cons, List.mem_nil_iff]
  <;>
  aesop
  -- !benchmark @end proof
