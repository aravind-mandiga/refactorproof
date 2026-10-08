-- !benchmark @start import type=solution
import Mathlib
import Aesop
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def DivisionFunction_precond (x : Nat) (y : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux
def divMod (x y : Nat) : Int × Int :=
  let q : Int := Int.ofNat (x / y)
  let r : Int := Int.ofNat (x % y)
  (r, q)
-- !benchmark @end code_aux


def DivisionFunction (x : Nat) (y : Nat) (h_precond : DivisionFunction_precond (x) (y)) : Int × Int :=
  -- !benchmark @start code
  let __rp_tmp_d01a8bb8 : Int × Int :=
    if y = 0 then (Int.ofNat x, 0) else divMod x y
  __rp_tmp_d01a8bb8
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def DivisionFunction_postcond (x : Nat) (y : Nat) (result: Int × Int) (h_precond : DivisionFunction_precond (x) (y)) :=
  -- !benchmark @start postcond
  let (r, q) := result;
  (y = 0 → r = Int.ofNat x ∧ q = 0) ∧
  (y ≠ 0 → (q * Int.ofNat y + r = Int.ofNat x) ∧ (0 ≤ r ∧ r < Int.ofNat y) ∧ (0 ≤ q))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem DivisionFunction_spec_satisfied (x: Nat) (y: Nat) (h_precond : DivisionFunction_precond (x) (y)) :
    DivisionFunction_postcond (x) (y) (DivisionFunction (x) (y) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold DivisionFunction DivisionFunction_postcond
  have h_main : DivisionFunction_postcond (x) (y) (DivisionFunction (x) (y) h_precond) h_precond := by
    by_cases hy : y = 0
    · -- Case: y = 0
      simp [DivisionFunction, hy, DivisionFunction_postcond, Int.ofNat_zero, Int.ofNat_add, Int.ofNat_mul,
        Int.ofNat_succ, Nat.cast_zero, Nat.cast_add, Nat.cast_mul, Nat.cast_succ]
      <;> aesop
    · -- Case: y ≠ 0
      have h₁ : y ≠ 0 := hy
      simp [DivisionFunction, h₁, divMod, DivisionFunction_postcond, Int.ofNat_zero, Int.ofNat_add,
        Int.ofNat_mul, Int.ofNat_succ, Nat.cast_zero, Nat.cast_add, Nat.cast_mul, Nat.cast_succ]
      have h₂ : (x : ℤ) / y * y + (x : ℤ) % y = x := by
        have h₃ : (x : ℤ) = (x : ℤ) / y * y + (x : ℤ) % y := by
          have h₄ : (x : ℤ) = (x : ℤ) / y * y + (x : ℤ) % y := by
            -- Use the property of division and modulus in integers
            have h₅ : (x : ℤ) % y = (x : ℤ) - (x : ℤ) / y * y := by
              have h₅₁ : (x : ℤ) % y = (x : ℤ) - (x : ℤ) / y * y := by
                rw [Int.emod_def]
                <;> ring_nf
                <;> norm_num
                <;> omega
              exact h₅₁
            rw [h₅]
            <;> ring_nf
            <;> norm_num
            <;> omega
          exact h₄
        linarith
      have h₃ : (x : ℤ) % y < (y : ℤ) := by
        have h₄ : (x : ℤ) % y < (y : ℤ) := by
          have h₅ : (x : ℤ) % y < (y : ℤ) := by
            -- Use the property of modulus in integers
            have h₆ : (x : ℤ) % y < (y : ℤ) := by
              apply Int.emod_lt_of_pos
              norm_cast
              <;> omega
            exact h₆
          exact h₅
        exact h₄
      have h₄ : 0 ≤ (x : ℤ) % y := by
        have h₅ : 0 ≤ (x : ℤ) % y := by
          apply Int.emod_nonneg
          norm_cast
          <;> omega
        exact h₅
      have h₅ : 0 ≤ (x : ℤ) / y := by
        have h₆ : 0 ≤ (x : ℤ) / y := by
          have h₇ : 0 ≤ (x : ℤ) / y := by
            -- Use the property of division in integers
            exact by
              have h₈ : 0 ≤ (x : ℤ) / y := by
                apply Int.ediv_nonneg
                <;> norm_cast
                <;> omega
              exact h₈
          exact h₇
        exact h₆
      constructor
      · -- Prove q * y + r = x
        simpa using h₂
      · constructor
        · -- Prove 0 ≤ r < y
          constructor
          · -- Prove 0 ≤ r
            simpa using h₄
          · -- Prove r < y
            simpa using h₃
        · -- Prove 0 ≤ q
          simpa using h₅
  exact h_main
  -- !benchmark @end proof
