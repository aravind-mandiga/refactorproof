-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def DoubleQuadruple_precond (x : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def DoubleQuadruple (x : Int) (h_precond : DoubleQuadruple_precond (x)) : (Int × Int) :=
  -- !benchmark @start code
  let a := 2 * x
  let b := a * 2
  (a, b)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def DoubleQuadruple_postcond (x : Int) (result: (Int × Int)) (h_precond : DoubleQuadruple_precond (x)) :=
  -- !benchmark @start postcond
  result.fst = 2 * x ∧ result.snd = 2 * result.fst
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem DoubleQuadruple_spec_satisfied (x: Int) (h_precond : DoubleQuadruple_precond (x)) :
    DoubleQuadruple_postcond (x) (DoubleQuadruple (x) h_precond) h_precond := by
  -- !benchmark @start proof
  have h₁ : (DoubleQuadruple (x) h_precond).fst = 2 * x := by
    dsimp [DoubleQuadruple, DoubleQuadruple_precond, Prod.fst]
    <;> ring_nf
    <;> simp_all
    <;> linarith

  have h₂ : (DoubleQuadruple (x) h_precond).snd = 2 * (DoubleQuadruple (x) h_precond).fst := by
    dsimp [DoubleQuadruple, DoubleQuadruple_precond, Prod.snd]
    <;> ring_nf
    <;> simp_all
    <;> linarith

  have h₃ : DoubleQuadruple_postcond (x) (DoubleQuadruple (x) h_precond) h_precond := by
    dsimp [DoubleQuadruple_postcond]
    exact ⟨h₁, h₂⟩

  exact h₃
  -- !benchmark @end proof
