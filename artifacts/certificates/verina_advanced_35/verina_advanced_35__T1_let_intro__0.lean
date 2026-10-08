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
  let __rp_tmp_559d5d0c : Int :=
    Id.run do
      let mut counts : HashMap Int Nat := {}
      let n := nums.length
      for x in nums do
        let count := counts.getD x 0
        counts := counts.insert x (count + 1)
      match counts.toList.find? (fun (_, c) => c > n / 2) with
      | some (k, _) => k
      | none      => 0
  __rp_tmp_559d5d0c
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
  (simp only [RPOrig.majorityElement, RPRef.majorityElement]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.majorityElement RPRef.majorityElement; rfl))

theorem rp_equiv_simp (nums : List Int) (h_precond : majorityElement_precond (nums)) :
    RPOrig.majorityElement nums h_precond = RPRef.majorityElement nums h_precond := by
  (simp [RPOrig.majorityElement, RPRef.majorityElement]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.majorityElement RPRef.majorityElement; rfl))
