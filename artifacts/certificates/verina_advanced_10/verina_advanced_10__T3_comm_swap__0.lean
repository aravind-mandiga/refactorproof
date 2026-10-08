-- !benchmark @start import type=task
import Mathlib.Data.Nat.Prime.Defs
-- !benchmark @end import

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
def removePrimeFactor (n : Nat) (p : Nat) : Nat :=
  if h : p > 1 ∧ n > 0 then
    if n % p = 0 then
      have : n / p < n := Nat.div_lt_self h.2 h.1
      removePrimeFactor (n / p) p
    else n
  else n
termination_by n

def removeAllPrimeFactors (n : Nat) (primes : List Nat) : Nat :=
  primes.foldl removePrimeFactor n
-- !benchmark @end precond_aux

@[reducible]
def findExponents_precond (n : Nat) (primes : List Nat) : Prop :=
  -- !benchmark @start precond
  n > 0 ∧
  primes.length > 0 ∧
  primes.all (fun p => Nat.Prime p) ∧
  List.Nodup primes ∧
  removeAllPrimeFactors n primes = 1
  -- !benchmark @end precond



namespace RPOrig

def findExponents (n : Nat) (primes : List Nat) (h_precond : findExponents_precond (n) (primes)) : List (Nat × Nat) :=
  let rec countFactors (n : Nat) (primes : List Nat) : List (Nat × Nat) :=
    match primes with
    | [] => []
    | p :: ps =>
      let (count, n') :=
        countFactor n p 0
      (p, count) :: countFactors n' ps

  countFactors n primes
  where

  countFactor : Nat → Nat → Nat → Nat × Nat
  | 0, _, count =>
    (count, 0)
  | n, p, count =>
    if h : n > 0 ∧ p > 1 then
      have : n / p < n :=
        Nat.div_lt_self h.1 h.2
      if n % p == 0 then
        countFactor (n / p) p (count + 1)
      else
        (count, n)
    else
      (count, n)
  termination_by n _ _ => n
end RPOrig

namespace RPRef

def findExponents (n : Nat) (primes : List Nat) (h_precond : findExponents_precond (n) (primes)) : List (Nat × Nat) :=
  let rec countFactors (n : Nat) (primes : List Nat) : List (Nat × Nat) :=
    match primes with
    | [] => []
    | p :: ps =>
      let (count, n') :=
        countFactor n p 0
      (p, count) :: countFactors n' ps

  countFactors n primes
  where

  countFactor : Nat → Nat → Nat → Nat × Nat
  | 0, _, count =>
    (count, 0)
  | n, p, count =>
    if h : n > 0 ∧ p > 1 then
      have : n / p < n :=
        Nat.div_lt_self h.1 h.2
      if n % p == 0 then
        countFactor (n / p) p (1 + count)
      else
        (count, n)
    else
      (count, n)
  termination_by n _ _ => n
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (n : Nat) (primes : List Nat) (h_precond : findExponents_precond (n) (primes)) :
    RPOrig.findExponents n primes h_precond = RPRef.findExponents n primes h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (n : Nat) (primes : List Nat) (h_precond : findExponents_precond (n) (primes)) :
    RPOrig.findExponents n primes h_precond = RPRef.findExponents n primes h_precond := rfl

theorem rp_equiv_delta_rfl (n : Nat) (primes : List Nat) (h_precond : findExponents_precond (n) (primes)) :
    RPOrig.findExponents n primes h_precond = RPRef.findExponents n primes h_precond := by
  delta RPOrig.findExponents RPRef.findExponents RPOrig.findExponents.countFactors RPRef.findExponents.countFactors
  rfl

theorem rp_equiv_simp_only (n : Nat) (primes : List Nat) (h_precond : findExponents_precond (n) (primes)) :
    RPOrig.findExponents n primes h_precond = RPRef.findExponents n primes h_precond := by
  first
    | (simp only [RPOrig.findExponents, RPRef.findExponents, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findExponents RPRef.findExponents RPOrig.findExponents.countFactors RPRef.findExponents.countFactors; rfl))
    | (simp only [RPOrig.findExponents, RPRef.findExponents, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findExponents RPRef.findExponents RPOrig.findExponents.countFactors RPRef.findExponents.countFactors; rfl))
    | (simp only [RPOrig.findExponents, RPRef.findExponents, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findExponents RPRef.findExponents RPOrig.findExponents.countFactors RPRef.findExponents.countFactors; rfl))
    | (simp only [RPOrig.findExponents, RPRef.findExponents]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findExponents RPRef.findExponents RPOrig.findExponents.countFactors RPRef.findExponents.countFactors; rfl))

theorem rp_equiv_simp (n : Nat) (primes : List Nat) (h_precond : findExponents_precond (n) (primes)) :
    RPOrig.findExponents n primes h_precond = RPRef.findExponents n primes h_precond := by
  first
    | (simp [RPOrig.findExponents, RPRef.findExponents, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findExponents RPRef.findExponents RPOrig.findExponents.countFactors RPRef.findExponents.countFactors; rfl))
    | (simp [RPOrig.findExponents, RPRef.findExponents, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findExponents RPRef.findExponents RPOrig.findExponents.countFactors RPRef.findExponents.countFactors; rfl))
    | (simp [RPOrig.findExponents, RPRef.findExponents, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findExponents RPRef.findExponents RPOrig.findExponents.countFactors RPRef.findExponents.countFactors; rfl))
    | (simp [RPOrig.findExponents, RPRef.findExponents]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findExponents RPRef.findExponents RPOrig.findExponents.countFactors RPRef.findExponents.countFactors; rfl))

theorem rp_equiv_ac_rfl (n : Nat) (primes : List Nat) (h_precond : findExponents_precond (n) (primes)) :
    RPOrig.findExponents n primes h_precond = RPRef.findExponents n primes h_precond := by
  (try simp only [RPOrig.findExponents, RPRef.findExponents]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findExponents RPRef.findExponents RPOrig.findExponents.countFactors RPRef.findExponents.countFactors; rfl))
