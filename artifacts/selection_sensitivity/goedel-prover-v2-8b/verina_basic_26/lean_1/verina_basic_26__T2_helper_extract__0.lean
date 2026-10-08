-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isEven_precond (n : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

private def isEven__rp_helper_3a986bdd (n : Int) (h_precond : isEven_precond (n)) : Bool :=
  n % 2 == 0
-- !benchmark @end code_aux


def isEven (n : Int) (h_precond : isEven_precond (n)) : Bool :=
  -- !benchmark @start code
  isEven__rp_helper_3a986bdd n h_precond
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def isEven_postcond (n : Int) (result: Bool) (h_precond : isEven_precond (n)) :=
  -- !benchmark @start postcond
  (result → n % 2 = 0) ∧ (¬ result → n % 2 ≠ 0)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem isEven_spec_satisfied (n: Int) (h_precond : isEven_precond (n)) :
    isEven_postcond (n) (isEven (n) h_precond) h_precond := by
  -- !benchmark @start proof
  have h₁ : (isEven (n) h_precond → n % 2 = 0) := by
    intro h
    -- Simplify the goal using the definition of `isEven`
    simp [isEven, Int.emod_eq_of_lt] at h ⊢
    <;>
    (try omega) <;>
    (try
      {
        cases n with
        | ofNat n =>
          simp_all [Int.emod_eq_of_lt]
          <;> omega
        | negSucc n =>
          simp_all [Int.emod_eq_of_lt]
          <;> omega
      }) <;>
    (try
      {
        simp_all [Int.emod_eq_of_lt]
        <;> omega
      })
    <;>
    (try omega)
    <;>
    (try
      {
        simp_all [Int.emod_eq_of_lt]
        <;> omega
      })
    <;>
    (try omega)

  have h₂ : (¬ isEven (n) h_precond → n % 2 ≠ 0) := by
    intro h
    -- Simplify the goal using the definition of `isEven`
    simp [isEven, Int.emod_eq_of_lt] at h ⊢
    <;>
    (try omega) <;>
    (try
      {
        cases n with
        | ofNat n =>
          simp_all [Int.emod_eq_of_lt]
          <;> omega
        | negSucc n =>
          simp_all [Int.emod_eq_of_lt]
          <;> omega
      }) <;>
    (try
      {
        simp_all [Int.emod_eq_of_lt]
        <;> omega
      })
    <;>
    (try omega)
    <;>
    (try
      {
        simp_all [Int.emod_eq_of_lt]
        <;> omega
      })
    <;>
    (try omega)

  have h₃ : isEven_postcond (n) (isEven (n) h_precond) h_precond := by
    constructor <;> simp_all [isEven_postcond, isEven, Int.emod_eq_of_lt]
    <;>
    (try omega) <;>
    (try
      {
        cases n with
        | ofNat n =>
          simp_all [Int.emod_eq_of_lt]
          <;> omega
        | negSucc n =>
          simp_all [Int.emod_eq_of_lt]
          <;> omega
      }) <;>
    (try
      {
        simp_all [Int.emod_eq_of_lt]
        <;> omega
      })
    <;>
    (try omega)
    <;>
    (try
      {
        simp_all [Int.emod_eq_of_lt]
        <;> omega
      })
    <;>
    (try omega)

  apply h₃
  -- !benchmark @end proof
