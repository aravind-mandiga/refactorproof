-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def insertionSort_precond (l : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
-- Helper function to insert an integer into a sorted list
def insertElement (x : Int) (l : List Int) : List Int :=
  match l with
  | [] => [x]
  | y :: ys =>
      if x <= y then
        x :: y :: ys
      else
        y :: insertElement x ys

-- Helper function to sort a list using insertion sort
def sortList (l : List Int) : List Int :=
  match l with
  | [] => []
  | x :: xs =>
      insertElement x (sortList xs)

namespace RPOrig

def insertionSort (l : List Int) (h_precond : insertionSort_precond (l)) : List Int :=
  let result := sortList l
  result
end RPOrig

namespace RPRef

private def insertionSort__rp_helper_153302ff (l : List Int) (h_precond : insertionSort_precond (l)) : List Int :=
  let result := sortList l
  result

def insertionSort (l : List Int) (h_precond : insertionSort_precond (l)) : List Int :=
  insertionSort__rp_helper_153302ff l h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (l : List Int) (h_precond : insertionSort_precond (l)) :
    RPOrig.insertionSort l h_precond = RPRef.insertionSort l h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (l : List Int) (h_precond : insertionSort_precond (l)) :
    RPOrig.insertionSort l h_precond = RPRef.insertionSort l h_precond := rfl

theorem rp_equiv_delta_rfl (l : List Int) (h_precond : insertionSort_precond (l)) :
    RPOrig.insertionSort l h_precond = RPRef.insertionSort l h_precond := by
  delta RPOrig.insertionSort RPRef.insertionSort RPRef.insertionSort__rp_helper_153302ff
  rfl

theorem rp_equiv_simp_only (l : List Int) (h_precond : insertionSort_precond (l)) :
    RPOrig.insertionSort l h_precond = RPRef.insertionSort l h_precond := by
  (simp only [RPOrig.insertionSort, RPRef.insertionSort, RPRef.insertionSort__rp_helper_153302ff]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.insertionSort RPRef.insertionSort RPRef.insertionSort__rp_helper_153302ff; rfl))

theorem rp_equiv_simp (l : List Int) (h_precond : insertionSort_precond (l)) :
    RPOrig.insertionSort l h_precond = RPRef.insertionSort l h_precond := by
  (simp [RPOrig.insertionSort, RPRef.insertionSort, RPRef.insertionSort__rp_helper_153302ff]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.insertionSort RPRef.insertionSort RPRef.insertionSort__rp_helper_153302ff; rfl))
