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
private def firstEvenOddDifference__rp_helper_33cb6d1d (a : Array Int) (h_precond : firstEvenOddDifference_precond (a)) : Int :=
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

def firstEvenOddDifference (a : Array Int) (h_precond : firstEvenOddDifference_precond (a)) : Int :=
  firstEvenOddDifference__rp_helper_33cb6d1d a h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (h_precond : firstEvenOddDifference_precond (a)) :
    RPOrig.firstEvenOddDifference a h_precond = RPRef.firstEvenOddDifference a h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (h_precond : firstEvenOddDifference_precond (a)) :
    RPOrig.firstEvenOddDifference a h_precond = RPRef.firstEvenOddDifference a h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (h_precond : firstEvenOddDifference_precond (a)) :
    RPOrig.firstEvenOddDifference a h_precond = RPRef.firstEvenOddDifference a h_precond := by
  delta RPOrig.firstEvenOddDifference RPRef.firstEvenOddDifference RPRef.firstEvenOddDifference__rp_helper_33cb6d1d RPOrig.firstEvenOddDifference.findFirstEvenOdd RPRef.firstEvenOddDifference__rp_helper_33cb6d1d.findFirstEvenOdd
  rfl

theorem rp_equiv_simp_only (a : Array Int) (h_precond : firstEvenOddDifference_precond (a)) :
    RPOrig.firstEvenOddDifference a h_precond = RPRef.firstEvenOddDifference a h_precond := by
  (simp only [RPOrig.firstEvenOddDifference, RPRef.firstEvenOddDifference, RPRef.firstEvenOddDifference__rp_helper_33cb6d1d]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.firstEvenOddDifference RPRef.firstEvenOddDifference RPRef.firstEvenOddDifference__rp_helper_33cb6d1d RPOrig.firstEvenOddDifference.findFirstEvenOdd RPRef.firstEvenOddDifference__rp_helper_33cb6d1d.findFirstEvenOdd; rfl))

theorem rp_equiv_simp (a : Array Int) (h_precond : firstEvenOddDifference_precond (a)) :
    RPOrig.firstEvenOddDifference a h_precond = RPRef.firstEvenOddDifference a h_precond := by
  (simp [RPOrig.firstEvenOddDifference, RPRef.firstEvenOddDifference, RPRef.firstEvenOddDifference__rp_helper_33cb6d1d]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.firstEvenOddDifference RPRef.firstEvenOddDifference RPRef.firstEvenOddDifference__rp_helper_33cb6d1d RPOrig.firstEvenOddDifference.findFirstEvenOdd RPRef.firstEvenOddDifference__rp_helper_33cb6d1d.findFirstEvenOdd; rfl))
