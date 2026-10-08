-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def mergeSorted_precond (a1 : Array Nat) (a2 : Array Nat) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· ≤ ·) a1.toList ∧ List.Pairwise (· ≤ ·) a2.toList
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def mergeLoop (a1 a2 : Array Nat) (i j : Nat) (result : Array Nat) : Nat × Nat × Array Nat :=
  if h : i < a1.size ∧ j < a2.size then
    if a1[i]! ≤ a2[j]! then
      mergeLoop a1 a2 (i + 1) j (result.push a1[i]!)
    else
      mergeLoop a1 a2 i (j + 1) (result.push a2[j]!)
  else
    (i, j, result)
termination_by a1.size - i + (a2.size - j)

def drain (arr : Array Nat) (i : Nat) (result : Array Nat) : Array Nat :=
  if h : i < arr.size then
    drain arr (i + 1) (result.push arr[i]!)
  else
    result
termination_by arr.size - i

namespace RPOrig

def mergeSorted (a1 : Array Nat) (a2 : Array Nat) (h_precond : mergeSorted_precond (a1) (a2)) : Array Nat :=
  let (i, j, result) := mergeLoop a1 a2 0 0 #[]
  let result := drain a1 i result
  let result := drain a2 j result
  result
end RPOrig

namespace RPRef

private def mergeSorted__rp_helper_a297d423 (a1 : Array Nat) (a2 : Array Nat) (h_precond : mergeSorted_precond (a1) (a2)) : Array Nat :=
  let (i, j, result) := mergeLoop a1 a2 0 0 #[]
  let result := drain a1 i result
  let result := drain a2 j result
  result

def mergeSorted (a1 : Array Nat) (a2 : Array Nat) (h_precond : mergeSorted_precond (a1) (a2)) : Array Nat :=
  mergeSorted__rp_helper_a297d423 a1 a2 h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a1 : Array Nat) (a2 : Array Nat) (h_precond : mergeSorted_precond (a1) (a2)) :
    RPOrig.mergeSorted a1 a2 h_precond = RPRef.mergeSorted a1 a2 h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a1 : Array Nat) (a2 : Array Nat) (h_precond : mergeSorted_precond (a1) (a2)) :
    RPOrig.mergeSorted a1 a2 h_precond = RPRef.mergeSorted a1 a2 h_precond := rfl

theorem rp_equiv_delta_rfl (a1 : Array Nat) (a2 : Array Nat) (h_precond : mergeSorted_precond (a1) (a2)) :
    RPOrig.mergeSorted a1 a2 h_precond = RPRef.mergeSorted a1 a2 h_precond := by
  delta RPOrig.mergeSorted RPRef.mergeSorted RPRef.mergeSorted__rp_helper_a297d423
  rfl

theorem rp_equiv_simp_only (a1 : Array Nat) (a2 : Array Nat) (h_precond : mergeSorted_precond (a1) (a2)) :
    RPOrig.mergeSorted a1 a2 h_precond = RPRef.mergeSorted a1 a2 h_precond := by
  (simp only [RPOrig.mergeSorted, RPRef.mergeSorted, RPRef.mergeSorted__rp_helper_a297d423]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.mergeSorted RPRef.mergeSorted RPRef.mergeSorted__rp_helper_a297d423; rfl))

theorem rp_equiv_simp (a1 : Array Nat) (a2 : Array Nat) (h_precond : mergeSorted_precond (a1) (a2)) :
    RPOrig.mergeSorted a1 a2 h_precond = RPRef.mergeSorted a1 a2 h_precond := by
  (simp [RPOrig.mergeSorted, RPRef.mergeSorted, RPRef.mergeSorted__rp_helper_a297d423]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.mergeSorted RPRef.mergeSorted RPRef.mergeSorted__rp_helper_a297d423; rfl))
