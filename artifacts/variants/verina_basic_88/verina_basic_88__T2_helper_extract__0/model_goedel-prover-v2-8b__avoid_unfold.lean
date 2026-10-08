-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def ToArray_precond (xs : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

private def ToArray__rp_helper_a2d904a6 (xs : List Int) (h_precond : ToArray_precond (xs)) : Array Int :=
  xs.toArray
-- !benchmark @end code_aux


def ToArray (xs : List Int) (h_precond : ToArray_precond (xs)) : Array Int :=
  -- !benchmark @start code
  ToArray__rp_helper_a2d904a6 xs h_precond
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def ToArray_postcond (xs : List Int) (result: Array Int) (h_precond : ToArray_precond (xs)) :=
  -- !benchmark @start postcond
  result.size = xs.length ∧ ∀ (i : Nat), i < xs.length → result[i]! = xs[i]!
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem ToArray_spec_satisfied (xs: List Int) (h_precond : ToArray_precond (xs)) :
    ToArray_postcond (xs) (ToArray (xs) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_size : ((ToArray (xs) h_precond) : Array Int).size = xs.length := by
    simp [ToArray]
    <;>
    aesop

  have h_element : ∀ (i : Nat), i < xs.length → ((ToArray (xs) h_precond) : Array Int)[i]! = xs[i]! := by
    intro i hi
    simp [ToArray]
    <;>
    aesop

  exact ⟨h_size, h_element⟩
  -- !benchmark @end proof
