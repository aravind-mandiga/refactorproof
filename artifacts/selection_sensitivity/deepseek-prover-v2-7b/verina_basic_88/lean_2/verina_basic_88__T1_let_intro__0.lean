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

-- !benchmark @end code_aux


def ToArray (xs : List Int) (h_precond : ToArray_precond (xs)) : Array Int :=
  -- !benchmark @start code
  let __rp_tmp_f2f9a284 : Array Int :=
    xs.toArray
  __rp_tmp_f2f9a284
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
  have h_size : (ToArray (xs) h_precond).size = xs.length := by
    simp [ToArray, ToArray_precond]
    <;> rfl

  have h_get : ∀ (i : Nat), i < xs.length → (ToArray (xs) h_precond)[i]! = xs[i]! := by
    intro i h
    simp [ToArray, ToArray_precond]
    <;>
    (try simp_all [List.get, List.getD])
    <;>
    (try simp_all [Array.get, Array.getD])
    <;>
    (try aesop)
    <;>
    (try simp_all [List.get, List.getD])
    <;>
    (try simp_all [Array.get, Array.getD])
    <;>
    (try aesop)
    <;>
    (try
      {
        cases xs <;> simp_all [List.get, List.getD, Array.get, Array.getD] <;>
        (try norm_num at * <;> aesop) <;>
        (try omega)
      })
    <;>
    (try
      {
        simp_all [List.get, List.getD, Array.get, Array.getD]
        <;>
        aesop
      })
    <;>
    (try
      {
        aesop
      })

  constructor
  · exact h_size
  · exact h_get
  -- !benchmark @end proof
