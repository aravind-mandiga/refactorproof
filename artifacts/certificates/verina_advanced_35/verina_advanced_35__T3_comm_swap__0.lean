-- !benchmark @start import type=solution
import Std.Data.HashMap
-- !benchmark @end import

-- !benchmark @start solution_aux
open Std
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def majorityElement_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  nums.length > 0 ∧ nums.any (fun x => nums.count x > nums.length / 2)
  -- !benchmark @end precond



namespace RPOrig

def majorityElement (nums : List Int) (h_precond : majorityElement_precond (nums)) : Int :=
  Id.run do
    let mut counts : HashMap Int Nat := {}
    let n := nums.length
    for x in nums do
      let count := counts.getD x 0
      counts := counts.insert x (count + 1)
    match counts.toList.find? (fun (_, c) => c > n / 2) with
    | some (k, _) => k
    | none      => 0
end RPOrig

namespace RPRef

def majorityElement (nums : List Int) (h_precond : majorityElement_precond (nums)) : Int :=
  Id.run do
    let mut counts : HashMap Int Nat := {}
    let n := nums.length
    for x in nums do
      let count := counts.getD x 0
      counts := counts.insert x (1 + count)
    match counts.toList.find? (fun (_, c) => c > n / 2) with
    | some (k, _) => k
    | none      => 0
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (nums : List Int) (h_precond : majorityElement_precond (nums)) :
    RPOrig.majorityElement nums h_precond = RPRef.majorityElement nums h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (nums : List Int) (h_precond : majorityElement_precond (nums)) :
    RPOrig.majorityElement nums h_precond = RPRef.majorityElement nums h_precond := rfl

theorem rp_equiv_delta_rfl (nums : List Int) (h_precond : majorityElement_precond (nums)) :
    RPOrig.majorityElement nums h_precond = RPRef.majorityElement nums h_precond := by
  delta RPOrig.majorityElement RPRef.majorityElement
  rfl

theorem rp_equiv_simp_only (nums : List Int) (h_precond : majorityElement_precond (nums)) :
    RPOrig.majorityElement nums h_precond = RPRef.majorityElement nums h_precond := by
  first
    | (simp only [RPOrig.majorityElement, RPRef.majorityElement, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.majorityElement RPRef.majorityElement; rfl))
    | (simp only [RPOrig.majorityElement, RPRef.majorityElement, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.majorityElement RPRef.majorityElement; rfl))
    | (simp only [RPOrig.majorityElement, RPRef.majorityElement, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.majorityElement RPRef.majorityElement; rfl))
    | (simp only [RPOrig.majorityElement, RPRef.majorityElement]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.majorityElement RPRef.majorityElement; rfl))

theorem rp_equiv_simp (nums : List Int) (h_precond : majorityElement_precond (nums)) :
    RPOrig.majorityElement nums h_precond = RPRef.majorityElement nums h_precond := by
  first
    | (simp [RPOrig.majorityElement, RPRef.majorityElement, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.majorityElement RPRef.majorityElement; rfl))
    | (simp [RPOrig.majorityElement, RPRef.majorityElement, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.majorityElement RPRef.majorityElement; rfl))
    | (simp [RPOrig.majorityElement, RPRef.majorityElement, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.majorityElement RPRef.majorityElement; rfl))
    | (simp [RPOrig.majorityElement, RPRef.majorityElement]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.majorityElement RPRef.majorityElement; rfl))

theorem rp_equiv_ac_rfl (nums : List Int) (h_precond : majorityElement_precond (nums)) :
    RPOrig.majorityElement nums h_precond = RPRef.majorityElement nums h_precond := by
  (try simp only [RPOrig.majorityElement, RPRef.majorityElement]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.majorityElement RPRef.majorityElement; rfl))
