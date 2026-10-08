-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux
def isSpaceCommaDot (c : Char) : Bool :=
  if c = ' ' then true
  else if c = ',' then true
  else if c = '.' then true
  else false
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def replaceWithColon_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

private def replaceWithColon__rp_helper_3e0fbdec (s : String) (h_precond : replaceWithColon_precond (s)) : String :=
  let cs := s.toList
  let cs' := cs.map (fun c => if isSpaceCommaDot c then ':' else c)
  String.mk cs'
-- !benchmark @end code_aux


def replaceWithColon (s : String) (h_precond : replaceWithColon_precond (s)) : String :=
  -- !benchmark @start code
  replaceWithColon__rp_helper_3e0fbdec s h_precond
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def replaceWithColon_postcond (s : String) (result: String) (h_precond : replaceWithColon_precond (s)) :=
  -- !benchmark @start postcond
  let cs := s.toList
  let cs' := result.toList
  result.length = s.length ∧
  (∀ i, i < s.length →
    (isSpaceCommaDot cs[i]! → cs'[i]! = ':') ∧
    (¬isSpaceCommaDot cs[i]! → cs'[i]! = cs[i]!))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem replaceWithColon_spec_satisfied (s: String) (h_precond : replaceWithColon_precond (s)) :
    replaceWithColon_postcond (s) (replaceWithColon (s) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_main : replaceWithColon_postcond (s) (replaceWithColon (s) h_precond) h_precond := by
    dsimp [replaceWithColon_precond, replaceWithColon_postcond, replaceWithColon]
    constructor
    · -- Prove that the length of the result is the same as the length of s
      simp [List.length_cons, List.length_eq_zero]
      <;>
      aesop
    · -- Prove that for each index i < s.length, the conditions hold
      intro i hi
      have h₁ : (s.toList.map (fun c => if isSpaceCommaDot c then ':' else c)) = (s.toList.map (fun c => if isSpaceCommaDot c then ':' else c)) := rfl
      simp_all [List.get, List.map, List.zipWith, List.zip, List.get]
      <;>
      (try aesop) <;>
      (try
        {
          by_cases h : isSpaceCommaDot (s.toList.get ⟨i, hi⟩) <;> simp_all [isSpaceCommaDot, List.get]
          <;>
          (try { aesop }) <;>
          (try { simp_all [List.get] }) <;>
          (try { aesop }) <;>
          (try { simp_all [List.get] }) <;>
          (try { aesop })
        }) <;>
      (try
        {
          aesop
        }) <;>
      (try
        {
          simp_all [List.get]
          <;>
          aesop
        })
      <;>
      aesop

  exact h_main
  -- !benchmark @end proof
