-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def mergeSortedLists_precond (arr1 : List Int) (arr2 : List Int) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· ≤ ·) arr1 ∧ List.Pairwise (· ≤ ·) arr2
  -- !benchmark @end precond



namespace RPOrig

def mergeSortedLists (arr1 : List Int) (arr2 : List Int) (h_precond : mergeSortedLists_precond (arr1) (arr2)) : List Int :=
  let rec merge (xs : List Int) (ys : List Int) : List Int :=
    match xs, ys with
    | [], _ => ys
    | _, [] => xs
    | x :: xt, y :: yt =>
      if x <= y then
        x :: merge xt (y :: yt)
      else
        y :: merge (x :: xt) yt

  merge arr1 arr2
end RPOrig

namespace RPRef

def mergeSortedLists (arr1 : List Int) (arr2 : List Int) (h_precond : mergeSortedLists_precond (arr1) (arr2)) : List Int :=
  let __rp_tmp_a10387fb : List Int :=
    let rec merge (xs : List Int) (ys : List Int) : List Int :=
      match xs, ys with
      | [], _ => ys
      | _, [] => xs
      | x :: xt, y :: yt =>
        if x <= y then
          x :: merge xt (y :: yt)
        else
          y :: merge (x :: xt) yt

    merge arr1 arr2
  __rp_tmp_a10387fb
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (arr1 : List Int) (arr2 : List Int) (h_precond : mergeSortedLists_precond (arr1) (arr2)) :
    RPOrig.mergeSortedLists arr1 arr2 h_precond = RPRef.mergeSortedLists arr1 arr2 h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (arr1 : List Int) (arr2 : List Int) (h_precond : mergeSortedLists_precond (arr1) (arr2)) :
    RPOrig.mergeSortedLists arr1 arr2 h_precond = RPRef.mergeSortedLists arr1 arr2 h_precond := rfl

theorem rp_equiv_delta_rfl (arr1 : List Int) (arr2 : List Int) (h_precond : mergeSortedLists_precond (arr1) (arr2)) :
    RPOrig.mergeSortedLists arr1 arr2 h_precond = RPRef.mergeSortedLists arr1 arr2 h_precond := by
  delta RPOrig.mergeSortedLists RPRef.mergeSortedLists RPOrig.mergeSortedLists.merge RPRef.mergeSortedLists.merge
  rfl

theorem rp_equiv_simp_only (arr1 : List Int) (arr2 : List Int) (h_precond : mergeSortedLists_precond (arr1) (arr2)) :
    RPOrig.mergeSortedLists arr1 arr2 h_precond = RPRef.mergeSortedLists arr1 arr2 h_precond := by
  (simp only [RPOrig.mergeSortedLists, RPRef.mergeSortedLists]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.mergeSortedLists RPRef.mergeSortedLists RPOrig.mergeSortedLists.merge RPRef.mergeSortedLists.merge; rfl))

theorem rp_equiv_simp (arr1 : List Int) (arr2 : List Int) (h_precond : mergeSortedLists_precond (arr1) (arr2)) :
    RPOrig.mergeSortedLists arr1 arr2 h_precond = RPRef.mergeSortedLists arr1 arr2 h_precond := by
  (simp [RPOrig.mergeSortedLists, RPRef.mergeSortedLists]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.mergeSortedLists RPRef.mergeSortedLists RPOrig.mergeSortedLists.merge RPRef.mergeSortedLists.merge; rfl))
