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

def insertionSort (xs : List Int) (h_precond : insertionSort_precond (xs)) : List Int :=
    let __rp_tmp_20925170 : List Int :=
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
    __rp_tmp_20925170
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (xs : List Int) (h_precond : insertionSort_precond (xs)) :
    RPOrig.insertionSort xs h_precond = RPRef.insertionSort xs h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (xs : List Int) (h_precond : insertionSort_precond (xs)) :
    RPOrig.insertionSort xs h_precond = RPRef.insertionSort xs h_precond := rfl

theorem rp_equiv_delta_rfl (xs : List Int) (h_precond : insertionSort_precond (xs)) :
    RPOrig.insertionSort xs h_precond = RPRef.insertionSort xs h_precond := by
  delta RPOrig.insertionSort RPRef.insertionSort RPOrig.insertionSort.insert RPOrig.insertionSort.sort RPRef.insertionSort.insert RPRef.insertionSort.sort
  rfl

theorem rp_equiv_simp_only (xs : List Int) (h_precond : insertionSort_precond (xs)) :
    RPOrig.insertionSort xs h_precond = RPRef.insertionSort xs h_precond := by
  (simp only [RPOrig.insertionSort, RPRef.insertionSort]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.insertionSort RPRef.insertionSort RPOrig.insertionSort.insert RPOrig.insertionSort.sort RPRef.insertionSort.insert RPRef.insertionSort.sort; rfl))

theorem rp_equiv_simp (xs : List Int) (h_precond : insertionSort_precond (xs)) :
    RPOrig.insertionSort xs h_precond = RPRef.insertionSort xs h_precond := by
  (simp [RPOrig.insertionSort, RPRef.insertionSort]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.insertionSort RPRef.insertionSort RPOrig.insertionSort.insert RPOrig.insertionSort.sort RPRef.insertionSort.insert RPRef.insertionSort.sort; rfl))
