-- !benchmark @start import type=solution
import Std.Data.HashSet
-- !benchmark @end import

-- !benchmark @start solution_aux
open Std
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def solution_precond (nums : List Nat) : Prop :=
  -- !benchmark @start precond
  1 ≤ nums.length ∧ nums.length ≤ 100 ∧ nums.all (fun x => 1 ≤ x ∧ x ≤ 100)
  -- !benchmark @end precond



namespace RPOrig

def solution (nums : List Nat) : Nat :=
  let n := nums.length
  let subarray := fun (i j : Nat) => (nums.drop i).take (j - i + 1)
  let distinctCount := fun (l : List Nat) =>
    let hashSet := l.foldl (fun (s : HashSet Nat) a => s.insert a) HashSet.emptyWithCapacity
    hashSet.size
  List.range n |>.foldl (fun acc i =>
    acc +
      (List.range (n - i) |>.foldl (fun acc' d =>
        let subarr := subarray i (i + d)
        let cnt := distinctCount subarr
        acc' + cnt * cnt
      ) 0)
  ) 0
end RPOrig

namespace RPRef

def solution (nums : List Nat) : Nat :=
  let n := nums.length
  let subarray := fun (i j : Nat) => (nums.drop i).take (j - i + 1)
  let distinctCount := fun (l : List Nat) =>
    let hashSet := l.foldl (fun (s : HashSet Nat) a => s.insert a) HashSet.emptyWithCapacity
    hashSet.size
  List.range n |>.foldl (fun acc i =>
    acc +
      (List.range (n - i) |>.foldl (fun acc' d =>
        let subarr := subarray i (d + i)
        let cnt := distinctCount subarr
        acc' + cnt * cnt
      ) 0)
  ) 0
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (nums : List Nat) :
    RPOrig.solution nums = RPRef.solution nums := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (nums : List Nat) :
    RPOrig.solution nums = RPRef.solution nums := rfl

theorem rp_equiv_delta_rfl (nums : List Nat) :
    RPOrig.solution nums = RPRef.solution nums := by
  delta RPOrig.solution RPRef.solution
  rfl

theorem rp_equiv_simp_only (nums : List Nat) :
    RPOrig.solution nums = RPRef.solution nums := by
  first
    | (simp only [RPOrig.solution, RPRef.solution, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.solution RPRef.solution; rfl))
    | (simp only [RPOrig.solution, RPRef.solution, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.solution RPRef.solution; rfl))
    | (simp only [RPOrig.solution, RPRef.solution, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.solution RPRef.solution; rfl))
    | (simp only [RPOrig.solution, RPRef.solution]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.solution RPRef.solution; rfl))

theorem rp_equiv_simp (nums : List Nat) :
    RPOrig.solution nums = RPRef.solution nums := by
  first
    | (simp [RPOrig.solution, RPRef.solution, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.solution RPRef.solution; rfl))
    | (simp [RPOrig.solution, RPRef.solution, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.solution RPRef.solution; rfl))
    | (simp [RPOrig.solution, RPRef.solution, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.solution RPRef.solution; rfl))
    | (simp [RPOrig.solution, RPRef.solution]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.solution RPRef.solution; rfl))

theorem rp_equiv_ac_rfl (nums : List Nat) :
    RPOrig.solution nums = RPRef.solution nums := by
  (try simp only [RPOrig.solution, RPRef.solution]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.solution RPRef.solution; rfl))
