-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def insertionSort_precond (xs : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def insertionSort (xs : List Int) (h_precond : insertionSort_precond (xs)) : List Int :=
    let rec insert (x : Int) (ys : List Int) : List Int :=
      match ys with
      | []      => [x]
      | y :: ys' =>
        if x <= y then
          x :: y :: ys'
        else
          y :: insert x ys'

    let rec sort (arr : List Int) : List Int :=
      match arr with
      | []      => []
      | x :: xs => insert x (sort xs)

    sort xs
end RPOrig

namespace RPRef
private def insertionSort__rp_helper_bb414813 (xs : List Int) (h_precond : insertionSort_precond (xs)) : List Int :=
    let rec insert (x : Int) (ys : List Int) : List Int :=
      match ys with
      | []      => [x]
      | y :: ys' =>
        if x <= y then
          x :: y :: ys'
        else
          y :: insert x ys'

    let rec sort (arr : List Int) : List Int :=
      match arr with
      | []      => []
      | x :: xs => insert x (sort xs)

    sort xs

def insertionSort (xs : List Int) (h_precond : insertionSort_precond (xs)) : List Int :=
    insertionSort__rp_helper_bb414813 xs h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (xs : List Int) (h_precond : insertionSort_precond (xs)) :
    RPOrig.insertionSort xs h_precond = RPRef.insertionSort xs h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (xs : List Int) (h_precond : insertionSort_precond (xs)) :
    RPOrig.insertionSort xs h_precond = RPRef.insertionSort xs h_precond := rfl

theorem rp_equiv_delta_rfl (xs : List Int) (h_precond : insertionSort_precond (xs)) :
    RPOrig.insertionSort xs h_precond = RPRef.insertionSort xs h_precond := by
  delta RPOrig.insertionSort RPRef.insertionSort RPRef.insertionSort__rp_helper_bb414813 RPOrig.insertionSort.insert RPOrig.insertionSort.sort RPRef.insertionSort__rp_helper_bb414813.insert RPRef.insertionSort__rp_helper_bb414813.sort
  rfl

theorem rp_equiv_simp_only (xs : List Int) (h_precond : insertionSort_precond (xs)) :
    RPOrig.insertionSort xs h_precond = RPRef.insertionSort xs h_precond := by
  (simp only [RPOrig.insertionSort, RPRef.insertionSort, RPRef.insertionSort__rp_helper_bb414813]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.insertionSort RPRef.insertionSort RPRef.insertionSort__rp_helper_bb414813 RPOrig.insertionSort.insert RPOrig.insertionSort.sort RPRef.insertionSort__rp_helper_bb414813.insert RPRef.insertionSort__rp_helper_bb414813.sort; rfl))

theorem rp_equiv_simp (xs : List Int) (h_precond : insertionSort_precond (xs)) :
    RPOrig.insertionSort xs h_precond = RPRef.insertionSort xs h_precond := by
  (simp [RPOrig.insertionSort, RPRef.insertionSort, RPRef.insertionSort__rp_helper_bb414813]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.insertionSort RPRef.insertionSort RPRef.insertionSort__rp_helper_bb414813 RPOrig.insertionSort.insert RPOrig.insertionSort.sort RPRef.insertionSort__rp_helper_bb414813.insert RPRef.insertionSort__rp_helper_bb414813.sort; rfl))
