-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def majorityElement_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  nums.length > 0 ∧ nums.any (fun x => nums.count x > nums.length / 2)  -- majority element must exist
  -- !benchmark @end precond



namespace RPOrig

def majorityElement (nums : List Int) (h_precond : majorityElement_precond (nums)) : Int :=
  let rec insert (x : Int) (xs : List Int) : List Int :=
    match xs with
    | [] => [x]
    | h :: t =>
      if x ≤ h then
        x :: h :: t
      else
        h :: insert x t

  let rec insertionSort (xs : List Int) : List Int :=
    match xs with
    | [] => []
    | h :: t =>
      let sortedTail := insertionSort t
      let sorted := insert h sortedTail
      sorted

  let getAt := fun (xs : List Int) (i : Nat) =>
    match xs.drop i with
    | [] => 0
    | h :: _ => h

  let sorted := insertionSort nums

  let len := sorted.length
  let mid := len / 2
  getAt sorted mid
end RPOrig

namespace RPRef

def majorityElement (nums : List Int) (h_precond : majorityElement_precond (nums)) : Int :=
  let __rp_tmp_c8945121 : Int :=
    let rec insert (x : Int) (xs : List Int) : List Int :=
      match xs with
      | [] => [x]
      | h :: t =>
        if x ≤ h then
          x :: h :: t
        else
          h :: insert x t

    let rec insertionSort (xs : List Int) : List Int :=
      match xs with
      | [] => []
      | h :: t =>
        let sortedTail := insertionSort t
        let sorted := insert h sortedTail
        sorted

    let getAt := fun (xs : List Int) (i : Nat) =>
      match xs.drop i with
      | [] => 0
      | h :: _ => h

    let sorted := insertionSort nums

    let len := sorted.length
    let mid := len / 2
    getAt sorted mid
  __rp_tmp_c8945121
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (nums : List Int) (h_precond : majorityElement_precond (nums)) :
    RPOrig.majorityElement nums h_precond = RPRef.majorityElement nums h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (nums : List Int) (h_precond : majorityElement_precond (nums)) :
    RPOrig.majorityElement nums h_precond = RPRef.majorityElement nums h_precond := rfl

theorem rp_equiv_delta_rfl (nums : List Int) (h_precond : majorityElement_precond (nums)) :
    RPOrig.majorityElement nums h_precond = RPRef.majorityElement nums h_precond := by
  delta RPOrig.majorityElement RPRef.majorityElement RPOrig.majorityElement.insert RPOrig.majorityElement.insertionSort RPRef.majorityElement.insert RPRef.majorityElement.insertionSort
  rfl

theorem rp_equiv_simp_only (nums : List Int) (h_precond : majorityElement_precond (nums)) :
    RPOrig.majorityElement nums h_precond = RPRef.majorityElement nums h_precond := by
  (simp only [RPOrig.majorityElement, RPRef.majorityElement]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.majorityElement RPRef.majorityElement RPOrig.majorityElement.insert RPOrig.majorityElement.insertionSort RPRef.majorityElement.insert RPRef.majorityElement.insertionSort; rfl))

theorem rp_equiv_simp (nums : List Int) (h_precond : majorityElement_precond (nums)) :
    RPOrig.majorityElement nums h_precond = RPRef.majorityElement nums h_precond := by
  (simp [RPOrig.majorityElement, RPRef.majorityElement]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.majorityElement RPRef.majorityElement RPOrig.majorityElement.insert RPOrig.majorityElement.insertionSort RPRef.majorityElement.insert RPRef.majorityElement.insertionSort; rfl))
