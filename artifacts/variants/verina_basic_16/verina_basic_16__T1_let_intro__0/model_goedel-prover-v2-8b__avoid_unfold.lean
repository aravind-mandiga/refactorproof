-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def replaceChars_precond (s : String) (oldChar : Char) (newChar : Char) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def replaceChars (s : String) (oldChar : Char) (newChar : Char) (h_precond : replaceChars_precond (s) (oldChar) (newChar)) : String :=
  -- !benchmark @start code
  let __rp_tmp_21cefeda : String :=
    let cs := s.toList
    let cs' := cs.map (fun c => if c = oldChar then newChar else c)
    String.mk cs'
  __rp_tmp_21cefeda
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def replaceChars_postcond (s : String) (oldChar : Char) (newChar : Char) (result: String) (h_precond : replaceChars_precond (s) (oldChar) (newChar)) :=
  -- !benchmark @start postcond
  let cs := s.toList
  let cs' := result.toList
  result.length = s.length ∧
  (∀ i, i < cs.length →
    (cs[i]! = oldChar → cs'[i]! = newChar) ∧
    (cs[i]! ≠ oldChar → cs'[i]! = cs[i]!))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem replaceChars_spec_satisfied (s: String) (oldChar: Char) (newChar: Char) (h_precond : replaceChars_precond (s) (oldChar) (newChar)) :
    replaceChars_postcond (s) (oldChar) (newChar) (replaceChars (s) (oldChar) (newChar) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_main : replaceChars_postcond (s) (oldChar) (newChar) (replaceChars (s) (oldChar) (newChar) h_precond) h_precond := by
    dsimp [replaceChars, replaceChars_precond, replaceChars_postcond]
    <;>
    (try decide) <;>
    (try simp_all [String.length, List.map, List.length, List.get]) <;>
    (try
      {
        ext i
        induction s using String.induction_on with
        | nil => simp_all
        | cons a s ih =>
          cases i with
          | zero =>
            simp_all [String.get, List.get]
            <;>
            aesop
          | succ i =>
            simp_all [String.get, List.get]
            <;>
            aesop
      }) <;>
    (try
      {
        simp_all [String.length, List.map, List.length, List.get]
        <;>
        aesop
      })
    <;>
    aesop
  exact h_main
  -- !benchmark @end proof
