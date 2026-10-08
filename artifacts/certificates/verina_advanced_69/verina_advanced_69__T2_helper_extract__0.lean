-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def searchInsert_precond (xs : List Int) (target : Int) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· < ·) xs
  -- !benchmark @end precond



namespace RPOrig

def searchInsert (xs : List Int) (target : Int) (h_precond : searchInsert_precond (xs) (target)) : Nat :=
  match xs with
  | [] =>
      0
  | _ :: _ =>
      let rec helper : List Int → Nat → Nat :=
        fun ys idx =>
          match ys with
          | [] =>
              idx
          | y :: ys' =>
              let isCurrent := y
              let currentIndex := idx
              let targetValue := target
              let condition := targetValue ≤ isCurrent
              if condition then
                currentIndex
              else
                let incrementedIndex := currentIndex + 1
                let rest := ys'
                helper rest incrementedIndex
      let startingIndex := 0
      let result := helper xs startingIndex
      result
end RPOrig

namespace RPRef
private def searchInsert__rp_helper_7b5ac4c4 (xs : List Int) (target : Int) (h_precond : searchInsert_precond (xs) (target)) : Nat :=
  match xs with
  | [] =>
      0
  | _ :: _ =>
      let rec helper : List Int → Nat → Nat :=
        fun ys idx =>
          match ys with
          | [] =>
              idx
          | y :: ys' =>
              let isCurrent := y
              let currentIndex := idx
              let targetValue := target
              let condition := targetValue ≤ isCurrent
              if condition then
                currentIndex
              else
                let incrementedIndex := currentIndex + 1
                let rest := ys'
                helper rest incrementedIndex
      let startingIndex := 0
      let result := helper xs startingIndex
      result

def searchInsert (xs : List Int) (target : Int) (h_precond : searchInsert_precond (xs) (target)) : Nat :=
  searchInsert__rp_helper_7b5ac4c4 xs target h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (xs : List Int) (target : Int) (h_precond : searchInsert_precond (xs) (target)) :
    RPOrig.searchInsert xs target h_precond = RPRef.searchInsert xs target h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (xs : List Int) (target : Int) (h_precond : searchInsert_precond (xs) (target)) :
    RPOrig.searchInsert xs target h_precond = RPRef.searchInsert xs target h_precond := rfl

theorem rp_equiv_delta_rfl (xs : List Int) (target : Int) (h_precond : searchInsert_precond (xs) (target)) :
    RPOrig.searchInsert xs target h_precond = RPRef.searchInsert xs target h_precond := by
  delta RPOrig.searchInsert RPRef.searchInsert RPRef.searchInsert__rp_helper_7b5ac4c4 RPOrig.searchInsert.helper RPRef.searchInsert__rp_helper_7b5ac4c4.helper
  rfl

theorem rp_equiv_simp_only (xs : List Int) (target : Int) (h_precond : searchInsert_precond (xs) (target)) :
    RPOrig.searchInsert xs target h_precond = RPRef.searchInsert xs target h_precond := by
  (simp only [RPOrig.searchInsert, RPRef.searchInsert, RPRef.searchInsert__rp_helper_7b5ac4c4]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.searchInsert RPRef.searchInsert RPRef.searchInsert__rp_helper_7b5ac4c4 RPOrig.searchInsert.helper RPRef.searchInsert__rp_helper_7b5ac4c4.helper; rfl))

theorem rp_equiv_simp (xs : List Int) (target : Int) (h_precond : searchInsert_precond (xs) (target)) :
    RPOrig.searchInsert xs target h_precond = RPRef.searchInsert xs target h_precond := by
  (simp [RPOrig.searchInsert, RPRef.searchInsert, RPRef.searchInsert__rp_helper_7b5ac4c4]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.searchInsert RPRef.searchInsert RPRef.searchInsert__rp_helper_7b5ac4c4 RPOrig.searchInsert.helper RPRef.searchInsert__rp_helper_7b5ac4c4.helper; rfl))
