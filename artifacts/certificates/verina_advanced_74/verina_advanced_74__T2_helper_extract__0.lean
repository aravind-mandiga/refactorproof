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
private def solution__rp_helper_df7f449c (nums : List Nat) : Nat :=
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

def solution (nums : List Nat) : Nat :=
  solution__rp_helper_df7f449c nums
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (nums : List Nat) :
    RPOrig.solution nums = RPRef.solution nums := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (nums : List Nat) :
    RPOrig.solution nums = RPRef.solution nums := rfl

theorem rp_equiv_delta_rfl (nums : List Nat) :
    RPOrig.solution nums = RPRef.solution nums := by
  delta RPOrig.solution RPRef.solution RPRef.solution__rp_helper_df7f449c
  rfl

theorem rp_equiv_simp_only (nums : List Nat) :
    RPOrig.solution nums = RPRef.solution nums := by
  (simp only [RPOrig.solution, RPRef.solution, RPRef.solution__rp_helper_df7f449c]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.solution RPRef.solution RPRef.solution__rp_helper_df7f449c; rfl))

theorem rp_equiv_simp (nums : List Nat) :
    RPOrig.solution nums = RPRef.solution nums := by
  (simp [RPOrig.solution, RPRef.solution, RPRef.solution__rp_helper_df7f449c]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.solution RPRef.solution RPRef.solution__rp_helper_df7f449c; rfl))
