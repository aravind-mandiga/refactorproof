-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def uniqueSorted_precond (arr : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def uniqueSorted (arr : List Int) (h_precond : uniqueSorted_precond (arr)) : List Int :=
  let rec insert (x : Int) (sorted : List Int) : List Int :=
  match sorted with
  | [] =>
    [x]
  | head :: tail =>
    if x <= head then
      x :: head :: tail
    else
      head :: insert x tail

let rec insertionSort (xs : List Int) : List Int :=
  match xs with
  | [] =>
    []
  | h :: t =>
    let sortedTail := insertionSort t
    insert h sortedTail

let removeDups : List Int → List Int
| xs =>
  let rec aux (remaining : List Int) (seen : List Int) (acc : List Int) : List Int :=
    match remaining with
    | [] =>
      acc.reverse
    | h :: t =>
      if h ∈ seen then
        aux t seen acc
      else
        aux t (h :: seen) (h :: acc)
  aux xs [] []

insertionSort (removeDups arr)
end RPOrig

namespace RPRef
private def uniqueSorted__rp_helper_3919ed7e (arr : List Int) (h_precond : uniqueSorted_precond (arr)) : List Int :=
  let rec insert (x : Int) (sorted : List Int) : List Int :=
  match sorted with
  | [] =>
    [x]
  | head :: tail =>
    if x <= head then
      x :: head :: tail
    else
      head :: insert x tail

let rec insertionSort (xs : List Int) : List Int :=
  match xs with
  | [] =>
    []
  | h :: t =>
    let sortedTail := insertionSort t
    insert h sortedTail

let removeDups : List Int → List Int
| xs =>
  let rec aux (remaining : List Int) (seen : List Int) (acc : List Int) : List Int :=
    match remaining with
    | [] =>
      acc.reverse
    | h :: t =>
      if h ∈ seen then
        aux t seen acc
      else
        aux t (h :: seen) (h :: acc)
  aux xs [] []

insertionSort (removeDups arr)

def uniqueSorted (arr : List Int) (h_precond : uniqueSorted_precond (arr)) : List Int :=
uniqueSorted__rp_helper_3919ed7e arr h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (arr : List Int) (h_precond : uniqueSorted_precond (arr)) :
    RPOrig.uniqueSorted arr h_precond = RPRef.uniqueSorted arr h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (arr : List Int) (h_precond : uniqueSorted_precond (arr)) :
    RPOrig.uniqueSorted arr h_precond = RPRef.uniqueSorted arr h_precond := rfl

theorem rp_equiv_delta_rfl (arr : List Int) (h_precond : uniqueSorted_precond (arr)) :
    RPOrig.uniqueSorted arr h_precond = RPRef.uniqueSorted arr h_precond := by
  delta RPOrig.uniqueSorted RPRef.uniqueSorted RPRef.uniqueSorted__rp_helper_3919ed7e RPOrig.uniqueSorted.insert RPOrig.uniqueSorted.insertionSort RPOrig.uniqueSorted.aux RPRef.uniqueSorted__rp_helper_3919ed7e.insert RPRef.uniqueSorted__rp_helper_3919ed7e.insertionSort RPRef.uniqueSorted__rp_helper_3919ed7e.aux
  rfl

theorem rp_equiv_simp_only (arr : List Int) (h_precond : uniqueSorted_precond (arr)) :
    RPOrig.uniqueSorted arr h_precond = RPRef.uniqueSorted arr h_precond := by
  (simp only [RPOrig.uniqueSorted, RPRef.uniqueSorted, RPRef.uniqueSorted__rp_helper_3919ed7e]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.uniqueSorted RPRef.uniqueSorted RPRef.uniqueSorted__rp_helper_3919ed7e RPOrig.uniqueSorted.insert RPOrig.uniqueSorted.insertionSort RPOrig.uniqueSorted.aux RPRef.uniqueSorted__rp_helper_3919ed7e.insert RPRef.uniqueSorted__rp_helper_3919ed7e.insertionSort RPRef.uniqueSorted__rp_helper_3919ed7e.aux; rfl))

theorem rp_equiv_simp (arr : List Int) (h_precond : uniqueSorted_precond (arr)) :
    RPOrig.uniqueSorted arr h_precond = RPRef.uniqueSorted arr h_precond := by
  (simp [RPOrig.uniqueSorted, RPRef.uniqueSorted, RPRef.uniqueSorted__rp_helper_3919ed7e]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.uniqueSorted RPRef.uniqueSorted RPRef.uniqueSorted__rp_helper_3919ed7e RPOrig.uniqueSorted.insert RPOrig.uniqueSorted.insertionSort RPOrig.uniqueSorted.aux RPRef.uniqueSorted__rp_helper_3919ed7e.insert RPRef.uniqueSorted__rp_helper_3919ed7e.insertionSort RPRef.uniqueSorted__rp_helper_3919ed7e.aux; rfl))
