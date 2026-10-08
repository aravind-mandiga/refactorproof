-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def maxStrength_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  nums ≠ []
  -- !benchmark @end precond



namespace RPOrig

def maxStrength (nums : List Int) (h_precond : maxStrength_precond (nums)) : Int :=
  let powerSet := fun (l : List Int) =>
    let n := l.length
    let masks := List.range (2^n)
    masks.map fun mask =>
      (List.range n).foldr (fun i acc =>
        if (mask.shiftRight i).land 1 == 1 then l[i]! :: acc else acc
      ) []

  let subsets := powerSet nums
  let nonEmpty := subsets.filter (· ≠ [])
  let products := List.map (fun subset =>
    List.foldl (fun acc x =>
      acc * x) (1 : Int) subset)
    nonEmpty
  (List.max? products).getD (-1000000)
end RPOrig

namespace RPRef
private def maxStrength__rp_helper_2ce7585c (nums : List Int) (h_precond : maxStrength_precond (nums)) : Int :=
  let powerSet := fun (l : List Int) =>
    let n := l.length
    let masks := List.range (2^n)
    masks.map fun mask =>
      (List.range n).foldr (fun i acc =>
        if (mask.shiftRight i).land 1 == 1 then l[i]! :: acc else acc
      ) []

  let subsets := powerSet nums
  let nonEmpty := subsets.filter (· ≠ [])
  let products := List.map (fun subset =>
    List.foldl (fun acc x =>
      acc * x) (1 : Int) subset)
    nonEmpty
  (List.max? products).getD (-1000000)

def maxStrength (nums : List Int) (h_precond : maxStrength_precond (nums)) : Int :=
  maxStrength__rp_helper_2ce7585c nums h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (nums : List Int) (h_precond : maxStrength_precond (nums)) :
    RPOrig.maxStrength nums h_precond = RPRef.maxStrength nums h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (nums : List Int) (h_precond : maxStrength_precond (nums)) :
    RPOrig.maxStrength nums h_precond = RPRef.maxStrength nums h_precond := rfl

theorem rp_equiv_delta_rfl (nums : List Int) (h_precond : maxStrength_precond (nums)) :
    RPOrig.maxStrength nums h_precond = RPRef.maxStrength nums h_precond := by
  delta RPOrig.maxStrength RPRef.maxStrength RPRef.maxStrength__rp_helper_2ce7585c
  rfl

theorem rp_equiv_simp_only (nums : List Int) (h_precond : maxStrength_precond (nums)) :
    RPOrig.maxStrength nums h_precond = RPRef.maxStrength nums h_precond := by
  (simp only [RPOrig.maxStrength, RPRef.maxStrength, RPRef.maxStrength__rp_helper_2ce7585c]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxStrength RPRef.maxStrength RPRef.maxStrength__rp_helper_2ce7585c; rfl))

theorem rp_equiv_simp (nums : List Int) (h_precond : maxStrength_precond (nums)) :
    RPOrig.maxStrength nums h_precond = RPRef.maxStrength nums h_precond := by
  (simp [RPOrig.maxStrength, RPRef.maxStrength, RPRef.maxStrength__rp_helper_2ce7585c]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxStrength RPRef.maxStrength RPRef.maxStrength__rp_helper_2ce7585c; rfl))
