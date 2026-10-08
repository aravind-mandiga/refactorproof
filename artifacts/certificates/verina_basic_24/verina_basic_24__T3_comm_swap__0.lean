-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux
def isEven (n : Int) : Bool :=
  n % 2 == 0

def isOdd (n : Int) : Bool :=
  n % 2 != 0
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def firstEvenOddDifference_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 1 ∧
  (∃ x ∈ a, isEven x) ∧
  (∃ x ∈ a, isOdd x)
  -- !benchmark @end precond



namespace RPOrig

def firstEvenOddDifference (a : Array Int) (h_precond : firstEvenOddDifference_precond (a)) : Int :=
  let rec findFirstEvenOdd (i : Nat) (firstEven firstOdd : Option Nat) : Int :=
    if i < a.size then
      let x := a[i]!
      let firstEven := if firstEven.isNone && isEven x then some i else firstEven
      let firstOdd := if firstOdd.isNone && isOdd x then some i else firstOdd
      match firstEven, firstOdd with
      | some e, some o => a[e]! - a[o]!
      | _, _ => findFirstEvenOdd (i + 1) firstEven firstOdd
    else
      -- This case is impossible due to h2, but we need a value
      0
  findFirstEvenOdd 0 none none
end RPOrig

namespace RPRef

def firstEvenOddDifference (a : Array Int) (h_precond : firstEvenOddDifference_precond (a)) : Int :=
  let rec findFirstEvenOdd (i : Nat) (firstEven firstOdd : Option Nat) : Int :=
    if i < a.size then
      let x := a[i]!
      let firstEven := if firstEven.isNone && isEven x then some i else firstEven
      let firstOdd := if firstOdd.isNone && isOdd x then some i else firstOdd
      match firstEven, firstOdd with
      | some e, some o => a[e]! - a[o]!
      | _, _ => findFirstEvenOdd (1 + i) firstEven firstOdd
    else
      -- This case is impossible due to h2, but we need a value
      0
  findFirstEvenOdd 0 none none
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (h_precond : firstEvenOddDifference_precond (a)) :
    RPOrig.firstEvenOddDifference a h_precond = RPRef.firstEvenOddDifference a h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (h_precond : firstEvenOddDifference_precond (a)) :
    RPOrig.firstEvenOddDifference a h_precond = RPRef.firstEvenOddDifference a h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (h_precond : firstEvenOddDifference_precond (a)) :
    RPOrig.firstEvenOddDifference a h_precond = RPRef.firstEvenOddDifference a h_precond := by
  delta RPOrig.firstEvenOddDifference RPRef.firstEvenOddDifference RPOrig.firstEvenOddDifference.findFirstEvenOdd RPRef.firstEvenOddDifference.findFirstEvenOdd
  rfl

theorem rp_equiv_simp_only (a : Array Int) (h_precond : firstEvenOddDifference_precond (a)) :
    RPOrig.firstEvenOddDifference a h_precond = RPRef.firstEvenOddDifference a h_precond := by
  first
    | (simp only [RPOrig.firstEvenOddDifference, RPRef.firstEvenOddDifference, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.firstEvenOddDifference RPRef.firstEvenOddDifference RPOrig.firstEvenOddDifference.findFirstEvenOdd RPRef.firstEvenOddDifference.findFirstEvenOdd; rfl))
    | (simp only [RPOrig.firstEvenOddDifference, RPRef.firstEvenOddDifference, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.firstEvenOddDifference RPRef.firstEvenOddDifference RPOrig.firstEvenOddDifference.findFirstEvenOdd RPRef.firstEvenOddDifference.findFirstEvenOdd; rfl))
    | (simp only [RPOrig.firstEvenOddDifference, RPRef.firstEvenOddDifference, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.firstEvenOddDifference RPRef.firstEvenOddDifference RPOrig.firstEvenOddDifference.findFirstEvenOdd RPRef.firstEvenOddDifference.findFirstEvenOdd; rfl))
    | (simp only [RPOrig.firstEvenOddDifference, RPRef.firstEvenOddDifference]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.firstEvenOddDifference RPRef.firstEvenOddDifference RPOrig.firstEvenOddDifference.findFirstEvenOdd RPRef.firstEvenOddDifference.findFirstEvenOdd; rfl))

theorem rp_equiv_simp (a : Array Int) (h_precond : firstEvenOddDifference_precond (a)) :
    RPOrig.firstEvenOddDifference a h_precond = RPRef.firstEvenOddDifference a h_precond := by
  first
    | (simp [RPOrig.firstEvenOddDifference, RPRef.firstEvenOddDifference, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.firstEvenOddDifference RPRef.firstEvenOddDifference RPOrig.firstEvenOddDifference.findFirstEvenOdd RPRef.firstEvenOddDifference.findFirstEvenOdd; rfl))
    | (simp [RPOrig.firstEvenOddDifference, RPRef.firstEvenOddDifference, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.firstEvenOddDifference RPRef.firstEvenOddDifference RPOrig.firstEvenOddDifference.findFirstEvenOdd RPRef.firstEvenOddDifference.findFirstEvenOdd; rfl))
    | (simp [RPOrig.firstEvenOddDifference, RPRef.firstEvenOddDifference, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.firstEvenOddDifference RPRef.firstEvenOddDifference RPOrig.firstEvenOddDifference.findFirstEvenOdd RPRef.firstEvenOddDifference.findFirstEvenOdd; rfl))
    | (simp [RPOrig.firstEvenOddDifference, RPRef.firstEvenOddDifference]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.firstEvenOddDifference RPRef.firstEvenOddDifference RPOrig.firstEvenOddDifference.findFirstEvenOdd RPRef.firstEvenOddDifference.findFirstEvenOdd; rfl))

theorem rp_equiv_ac_rfl (a : Array Int) (h_precond : firstEvenOddDifference_precond (a)) :
    RPOrig.firstEvenOddDifference a h_precond = RPRef.firstEvenOddDifference a h_precond := by
  (try simp only [RPOrig.firstEvenOddDifference, RPRef.firstEvenOddDifference]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.firstEvenOddDifference RPRef.firstEvenOddDifference RPOrig.firstEvenOddDifference.findFirstEvenOdd RPRef.firstEvenOddDifference.findFirstEvenOdd; rfl))
