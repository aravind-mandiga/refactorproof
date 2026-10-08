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
      x * acc) (1 : Int) subset)
    nonEmpty
  (List.max? products).getD (-1000000)
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (nums : List Int) (h_precond : maxStrength_precond (nums)) :
    RPOrig.maxStrength nums h_precond = RPRef.maxStrength nums h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (nums : List Int) (h_precond : maxStrength_precond (nums)) :
    RPOrig.maxStrength nums h_precond = RPRef.maxStrength nums h_precond := rfl

theorem rp_equiv_delta_rfl (nums : List Int) (h_precond : maxStrength_precond (nums)) :
    RPOrig.maxStrength nums h_precond = RPRef.maxStrength nums h_precond := by
  delta RPOrig.maxStrength RPRef.maxStrength
  rfl

theorem rp_equiv_simp_only (nums : List Int) (h_precond : maxStrength_precond (nums)) :
    RPOrig.maxStrength nums h_precond = RPRef.maxStrength nums h_precond := by
  first
    | (simp only [RPOrig.maxStrength, RPRef.maxStrength, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxStrength RPRef.maxStrength; rfl))
    | (simp only [RPOrig.maxStrength, RPRef.maxStrength, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxStrength RPRef.maxStrength; rfl))
    | (simp only [RPOrig.maxStrength, RPRef.maxStrength, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxStrength RPRef.maxStrength; rfl))
    | (simp only [RPOrig.maxStrength, RPRef.maxStrength]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxStrength RPRef.maxStrength; rfl))

theorem rp_equiv_simp (nums : List Int) (h_precond : maxStrength_precond (nums)) :
    RPOrig.maxStrength nums h_precond = RPRef.maxStrength nums h_precond := by
  first
    | (simp [RPOrig.maxStrength, RPRef.maxStrength, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxStrength RPRef.maxStrength; rfl))
    | (simp [RPOrig.maxStrength, RPRef.maxStrength, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxStrength RPRef.maxStrength; rfl))
    | (simp [RPOrig.maxStrength, RPRef.maxStrength, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxStrength RPRef.maxStrength; rfl))
    | (simp [RPOrig.maxStrength, RPRef.maxStrength]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxStrength RPRef.maxStrength; rfl))

theorem rp_equiv_ac_rfl (nums : List Int) (h_precond : maxStrength_precond (nums)) :
    RPOrig.maxStrength nums h_precond = RPRef.maxStrength nums h_precond := by
  (try simp only [RPOrig.maxStrength, RPRef.maxStrength]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxStrength RPRef.maxStrength; rfl))
