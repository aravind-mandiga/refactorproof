-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def nextGreaterElement_precond (nums1 : List Int) (nums2 : List Int) : Prop :=
  -- !benchmark @start precond
  List.Nodup nums1 ∧
  List.Nodup nums2 ∧
  nums1.all (fun x => x ∈ nums2)
  -- !benchmark @end precond



namespace RPOrig

def nextGreaterElement (nums1 : List Int) (nums2 : List Int) (h_precond : nextGreaterElement_precond (nums1) (nums2)) : List Int :=
  let len1 := nums1.length

  let buildNextGreaterMap : List (Int × Int) :=
    let rec mapLoop (index : Nat) (stack : List Nat) (map : List (Int × Int)) : List (Int × Int) :=
      if h : index >= nums2.length then
        stack.foldl (fun acc pos => (nums2[pos]!, -1) :: acc) map
      else
        let currentValue := nums2[index]!

        let rec processStack (s : List Nat) (m : List (Int × Int)) : List Nat × List (Int × Int) :=
          match s with
          | [] => ([], m)
          | topIndex :: rest =>
              let topValue := nums2[topIndex]!
              if currentValue > topValue then
                let newMap := (topValue, currentValue) :: m
                processStack rest newMap
              else
                (s, m)

        let (newStack, newMap) := processStack stack map

        mapLoop (index + 1) (index :: newStack) newMap
      termination_by nums2.length - index

    mapLoop 0 [] []

  let buildResult : List Int :=
    let rec resultLoop (i : Nat) (result : List Int) : List Int :=
      if i >= len1 then
        result.reverse
      else
        let val := nums1[i]!
        let rec findInMap (m : List (Int × Int)) : Int :=
          match m with
          | [] => -1
          | (num, nextGreater) :: rest =>
              if num == val then nextGreater
              else findInMap rest

        let nextGreater := findInMap buildNextGreaterMap
        resultLoop (i + 1) (nextGreater :: result)
      termination_by len1 - i

    resultLoop 0 []

  buildResult
end RPOrig

namespace RPRef
private def nextGreaterElement__rp_helper_a6d69d4b (nums1 : List Int) (nums2 : List Int) (h_precond : nextGreaterElement_precond (nums1) (nums2)) : List Int :=
  let len1 := nums1.length

  let buildNextGreaterMap : List (Int × Int) :=
    let rec mapLoop (index : Nat) (stack : List Nat) (map : List (Int × Int)) : List (Int × Int) :=
      if h : index >= nums2.length then
        stack.foldl (fun acc pos => (nums2[pos]!, -1) :: acc) map
      else
        let currentValue := nums2[index]!

        let rec processStack (s : List Nat) (m : List (Int × Int)) : List Nat × List (Int × Int) :=
          match s with
          | [] => ([], m)
          | topIndex :: rest =>
              let topValue := nums2[topIndex]!
              if currentValue > topValue then
                let newMap := (topValue, currentValue) :: m
                processStack rest newMap
              else
                (s, m)

        let (newStack, newMap) := processStack stack map

        mapLoop (index + 1) (index :: newStack) newMap
      termination_by nums2.length - index

    mapLoop 0 [] []

  let buildResult : List Int :=
    let rec resultLoop (i : Nat) (result : List Int) : List Int :=
      if i >= len1 then
        result.reverse
      else
        let val := nums1[i]!
        let rec findInMap (m : List (Int × Int)) : Int :=
          match m with
          | [] => -1
          | (num, nextGreater) :: rest =>
              if num == val then nextGreater
              else findInMap rest

        let nextGreater := findInMap buildNextGreaterMap
        resultLoop (i + 1) (nextGreater :: result)
      termination_by len1 - i

    resultLoop 0 []

  buildResult

def nextGreaterElement (nums1 : List Int) (nums2 : List Int) (h_precond : nextGreaterElement_precond (nums1) (nums2)) : List Int :=
  nextGreaterElement__rp_helper_a6d69d4b nums1 nums2 h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (nums1 : List Int) (nums2 : List Int) (h_precond : nextGreaterElement_precond (nums1) (nums2)) :
    RPOrig.nextGreaterElement nums1 nums2 h_precond = RPRef.nextGreaterElement nums1 nums2 h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (nums1 : List Int) (nums2 : List Int) (h_precond : nextGreaterElement_precond (nums1) (nums2)) :
    RPOrig.nextGreaterElement nums1 nums2 h_precond = RPRef.nextGreaterElement nums1 nums2 h_precond := rfl

theorem rp_equiv_delta_rfl (nums1 : List Int) (nums2 : List Int) (h_precond : nextGreaterElement_precond (nums1) (nums2)) :
    RPOrig.nextGreaterElement nums1 nums2 h_precond = RPRef.nextGreaterElement nums1 nums2 h_precond := by
  first
    | (delta RPOrig.nextGreaterElement RPRef.nextGreaterElement RPRef.nextGreaterElement__rp_helper_a6d69d4b RPOrig.nextGreaterElement.mapLoop RPOrig.nextGreaterElement.mapLoop.processStack RPOrig.nextGreaterElement.resultLoop RPOrig.nextGreaterElement.resultLoop.findInMap RPRef.nextGreaterElement__rp_helper_a6d69d4b.mapLoop RPRef.nextGreaterElement__rp_helper_a6d69d4b.mapLoop.processStack RPRef.nextGreaterElement__rp_helper_a6d69d4b.resultLoop RPRef.nextGreaterElement__rp_helper_a6d69d4b.resultLoop.findInMap; rfl)
    | (delta RPOrig.nextGreaterElement RPRef.nextGreaterElement RPRef.nextGreaterElement__rp_helper_a6d69d4b RPOrig.nextGreaterElement.mapLoop RPOrig.nextGreaterElement.mapLoop.processStack RPOrig.nextGreaterElement.resultLoop RPOrig.nextGreaterElement.resultLoop.findInMap RPRef.nextGreaterElement__rp_helper_a6d69d4b.mapLoop RPRef.nextGreaterElement__rp_helper_a6d69d4b.mapLoop.processStack RPRef.nextGreaterElement__rp_helper_a6d69d4b.resultLoop RPRef.nextGreaterElement__rp_helper_a6d69d4b.resultLoop.findInMap RPOrig.nextGreaterElement._unary RPOrig.nextGreaterElement.mapLoop._unary RPOrig.nextGreaterElement.mapLoop.processStack._unary RPOrig.nextGreaterElement.resultLoop._unary RPOrig.nextGreaterElement.resultLoop.findInMap._unary RPRef.nextGreaterElement__rp_helper_a6d69d4b.mapLoop._unary RPRef.nextGreaterElement__rp_helper_a6d69d4b.mapLoop.processStack._unary RPRef.nextGreaterElement__rp_helper_a6d69d4b.resultLoop._unary RPRef.nextGreaterElement__rp_helper_a6d69d4b.resultLoop.findInMap._unary; rfl)
    | (set_option smartUnfolding false in rfl)

theorem rp_equiv_simp_only (nums1 : List Int) (nums2 : List Int) (h_precond : nextGreaterElement_precond (nums1) (nums2)) :
    RPOrig.nextGreaterElement nums1 nums2 h_precond = RPRef.nextGreaterElement nums1 nums2 h_precond := by
  (simp only [RPOrig.nextGreaterElement, RPRef.nextGreaterElement, RPRef.nextGreaterElement__rp_helper_a6d69d4b]) <;> (first | rfl | (delta RPOrig.nextGreaterElement RPRef.nextGreaterElement RPRef.nextGreaterElement__rp_helper_a6d69d4b RPOrig.nextGreaterElement.mapLoop RPOrig.nextGreaterElement.mapLoop.processStack RPOrig.nextGreaterElement.resultLoop RPOrig.nextGreaterElement.resultLoop.findInMap RPRef.nextGreaterElement__rp_helper_a6d69d4b.mapLoop RPRef.nextGreaterElement__rp_helper_a6d69d4b.mapLoop.processStack RPRef.nextGreaterElement__rp_helper_a6d69d4b.resultLoop RPRef.nextGreaterElement__rp_helper_a6d69d4b.resultLoop.findInMap; rfl) | (delta RPOrig.nextGreaterElement RPRef.nextGreaterElement RPRef.nextGreaterElement__rp_helper_a6d69d4b RPOrig.nextGreaterElement.mapLoop RPOrig.nextGreaterElement.mapLoop.processStack RPOrig.nextGreaterElement.resultLoop RPOrig.nextGreaterElement.resultLoop.findInMap RPRef.nextGreaterElement__rp_helper_a6d69d4b.mapLoop RPRef.nextGreaterElement__rp_helper_a6d69d4b.mapLoop.processStack RPRef.nextGreaterElement__rp_helper_a6d69d4b.resultLoop RPRef.nextGreaterElement__rp_helper_a6d69d4b.resultLoop.findInMap RPOrig.nextGreaterElement._unary RPOrig.nextGreaterElement.mapLoop._unary RPOrig.nextGreaterElement.mapLoop.processStack._unary RPOrig.nextGreaterElement.resultLoop._unary RPOrig.nextGreaterElement.resultLoop.findInMap._unary RPRef.nextGreaterElement__rp_helper_a6d69d4b.mapLoop._unary RPRef.nextGreaterElement__rp_helper_a6d69d4b.mapLoop.processStack._unary RPRef.nextGreaterElement__rp_helper_a6d69d4b.resultLoop._unary RPRef.nextGreaterElement__rp_helper_a6d69d4b.resultLoop.findInMap._unary; rfl) | (set_option smartUnfolding false in rfl))

theorem rp_equiv_simp (nums1 : List Int) (nums2 : List Int) (h_precond : nextGreaterElement_precond (nums1) (nums2)) :
    RPOrig.nextGreaterElement nums1 nums2 h_precond = RPRef.nextGreaterElement nums1 nums2 h_precond := by
  (simp [RPOrig.nextGreaterElement, RPRef.nextGreaterElement, RPRef.nextGreaterElement__rp_helper_a6d69d4b]) <;> (first | rfl | (delta RPOrig.nextGreaterElement RPRef.nextGreaterElement RPRef.nextGreaterElement__rp_helper_a6d69d4b RPOrig.nextGreaterElement.mapLoop RPOrig.nextGreaterElement.mapLoop.processStack RPOrig.nextGreaterElement.resultLoop RPOrig.nextGreaterElement.resultLoop.findInMap RPRef.nextGreaterElement__rp_helper_a6d69d4b.mapLoop RPRef.nextGreaterElement__rp_helper_a6d69d4b.mapLoop.processStack RPRef.nextGreaterElement__rp_helper_a6d69d4b.resultLoop RPRef.nextGreaterElement__rp_helper_a6d69d4b.resultLoop.findInMap; rfl) | (delta RPOrig.nextGreaterElement RPRef.nextGreaterElement RPRef.nextGreaterElement__rp_helper_a6d69d4b RPOrig.nextGreaterElement.mapLoop RPOrig.nextGreaterElement.mapLoop.processStack RPOrig.nextGreaterElement.resultLoop RPOrig.nextGreaterElement.resultLoop.findInMap RPRef.nextGreaterElement__rp_helper_a6d69d4b.mapLoop RPRef.nextGreaterElement__rp_helper_a6d69d4b.mapLoop.processStack RPRef.nextGreaterElement__rp_helper_a6d69d4b.resultLoop RPRef.nextGreaterElement__rp_helper_a6d69d4b.resultLoop.findInMap RPOrig.nextGreaterElement._unary RPOrig.nextGreaterElement.mapLoop._unary RPOrig.nextGreaterElement.mapLoop.processStack._unary RPOrig.nextGreaterElement.resultLoop._unary RPOrig.nextGreaterElement.resultLoop.findInMap._unary RPRef.nextGreaterElement__rp_helper_a6d69d4b.mapLoop._unary RPRef.nextGreaterElement__rp_helper_a6d69d4b.mapLoop.processStack._unary RPRef.nextGreaterElement__rp_helper_a6d69d4b.resultLoop._unary RPRef.nextGreaterElement__rp_helper_a6d69d4b.resultLoop.findInMap._unary; rfl) | (set_option smartUnfolding false in rfl))
