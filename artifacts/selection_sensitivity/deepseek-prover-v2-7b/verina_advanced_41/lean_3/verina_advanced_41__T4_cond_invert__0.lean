-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def maxOfThree_precond (a : Int) (b : Int) (c : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def maxOfThree (a : Int) (b : Int) (c : Int) (h_precond : maxOfThree_precond (a) (b) (c)) : Int :=
  -- !benchmark @start code
  if ¬ (a >= b && a >= c) then if b >= a && b >= c then b
  else c
  else a
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def maxOfThree_postcond (a : Int) (b : Int) (c : Int) (result: Int) (h_precond : maxOfThree_precond (a) (b) (c)) : Prop :=
  -- !benchmark @start postcond
  (result >= a ∧ result >= b ∧ result >= c) ∧ (result = a ∨ result = b ∨ result = c)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem maxOfThree_spec_satisfied (a: Int) (b: Int) (c: Int) (h_precond : maxOfThree_precond (a) (b) (c)) :
    maxOfThree_postcond (a) (b) (c) (maxOfThree (a) (b) (c) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_main : (maxOfThree a b c h_precond) ≥ a ∧ (maxOfThree a b c h_precond) ≥ b ∧ (maxOfThree a b c h_precond) ≥ c := by
    simp only [maxOfThree, maxOfThree_precond, true_and]
    split_ifs <;> simp_all (config := {decide := true}) <;>
    (try { contradiction }) <;>
    (try { omega }) <;>
    (try {
      constructor <;> (try constructor) <;>
      (try omega) <;> (try nlinarith)
    }) <;>
    (try {
      cases' le_total a b with hab hab <;> cases' le_total a c with hac hac <;>
        cases' le_total b c with hbc hbc <;> simp_all [max_eq_left, max_eq_right, le_refl, le_trans] <;>
        (try omega) <;> (try nlinarith)
    })
    <;>
    (try { omega }) <;>
    (try { nlinarith })

  have h_main₂ : (maxOfThree a b c h_precond) = a ∨ (maxOfThree a b c h_precond) = b ∨ (maxOfThree a b c h_precond) = c := by
    simp only [maxOfThree, maxOfThree_precond, true_and] at *
    split_ifs <;> simp_all (config := {decide := true}) <;>
    (try { aesop }) <;>
    (try { omega }) <;>
    (try {
      cases' le_total a b with hab hab <;> cases' le_total a c with hac hac <;>
        cases' le_total b c with hbc hbc <;> simp_all [max_eq_left, max_eq_right, le_refl, le_trans] <;>
        (try omega) <;> (try aesop) }) <;>
    aesop

  constructor <;>
  (try aesop) <;>
  (try
    {
      aesop
    }) <;>
  (try
    {
      simp_all [maxOfThree_postcond]
      <;> aesop
    }) <;>
  (try
    {
      rcases h_main₂ with (h₂ | h₂ | h₂) <;>
        aesop
    }) <;>
  (try
    {
      rcases h_main with ⟨h₁, h₂, h₃⟩ <;>
        aesop
    })
  <;>
  (try
    {
      aesop
    })
  <;>
  aesop
  -- !benchmark @end proof


