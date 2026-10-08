-- !benchmark @start import type=solution
import Mathlib
import Aesop
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def minOfThree_precond (a : Int) (b : Int) (c : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

private def minOfThree__rp_helper_d6baf0a7 (a : Int) (b : Int) (c : Int) (h_precond : minOfThree_precond (a) (b) (c)) : Int :=
  if a <= b && a <= c then a
  else if b <= a && b <= c then b
  else c
-- !benchmark @end code_aux


def minOfThree (a : Int) (b : Int) (c : Int) (h_precond : minOfThree_precond (a) (b) (c)) : Int :=
  -- !benchmark @start code
  minOfThree__rp_helper_d6baf0a7 a b c h_precond
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def minOfThree_postcond (a : Int) (b : Int) (c : Int) (result: Int) (h_precond : minOfThree_precond (a) (b) (c)) :=
  -- !benchmark @start postcond
  (result <= a ∧ result <= b ∧ result <= c) ∧
  (result = a ∨ result = b ∨ result = c)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem minOfThree_spec_satisfied (a: Int) (b: Int) (c: Int) (h_precond : minOfThree_precond (a) (b) (c)) :
    minOfThree_postcond (a) (b) (c) (minOfThree (a) (b) (c) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_main : minOfThree_postcond (a) (b) (c) (minOfThree (a) (b) (c) h_precond) h_precond := by
    dsimp only [minOfThree, minOfThree_precond, minOfThree_postcond] at *
    split_ifs at * <;>
    (try { contradiction }) <;>
    (try {
      simp_all [Int.le_of_lt]
      <;>
      (try { omega }) <;>
      (try {
        norm_num at *
        <;>
        (try { omega }) <;>
        (try {
          aesop
        })
      })
    }) <;>
    (try {
      aesop
    }) <;>
    (try {
      omega
    }) <;>
    (try {
      norm_num at *
      <;>
      aesop
    }) <;>
    (try {
      omega
    }) <;>
    (try {
      aesop
    })
    <;>
    (try {
      omega
    })
    <;>
    (try {
      aesop
    })
  exact h_main
  -- !benchmark @end proof
