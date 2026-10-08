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

        mapLoop (1 + index) (index :: newStack) newMap
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
    | (delta RPOrig.nextGreaterElement RPRef.nextGreaterElement RPOrig.nextGreaterElement.mapLoop RPOrig.nextGreaterElement.mapLoop.processStack RPOrig.nextGreaterElement.resultLoop RPOrig.nextGreaterElement.resultLoop.findInMap RPRef.nextGreaterElement.mapLoop RPRef.nextGreaterElement.mapLoop.processStack RPRef.nextGreaterElement.resultLoop RPRef.nextGreaterElement.resultLoop.findInMap; rfl)
    | (delta RPOrig.nextGreaterElement RPRef.nextGreaterElement RPOrig.nextGreaterElement.mapLoop RPOrig.nextGreaterElement.mapLoop.processStack RPOrig.nextGreaterElement.resultLoop RPOrig.nextGreaterElement.resultLoop.findInMap RPRef.nextGreaterElement.mapLoop RPRef.nextGreaterElement.mapLoop.processStack RPRef.nextGreaterElement.resultLoop RPRef.nextGreaterElement.resultLoop.findInMap RPOrig.nextGreaterElement._unary RPOrig.nextGreaterElement.mapLoop._unary RPOrig.nextGreaterElement.mapLoop.processStack._unary RPOrig.nextGreaterElement.resultLoop._unary RPOrig.nextGreaterElement.resultLoop.findInMap._unary RPRef.nextGreaterElement.mapLoop._unary RPRef.nextGreaterElement.mapLoop.processStack._unary RPRef.nextGreaterElement.resultLoop._unary RPRef.nextGreaterElement.resultLoop.findInMap._unary; rfl)
    | (set_option smartUnfolding false in rfl)

theorem rp_equiv_simp_only (nums1 : List Int) (nums2 : List Int) (h_precond : nextGreaterElement_precond (nums1) (nums2)) :
    RPOrig.nextGreaterElement nums1 nums2 h_precond = RPRef.nextGreaterElement nums1 nums2 h_precond := by
  first
    | (simp only [RPOrig.nextGreaterElement, RPRef.nextGreaterElement, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (delta RPOrig.nextGreaterElement RPRef.nextGreaterElement RPOrig.nextGreaterElement.mapLoop RPOrig.nextGreaterElement.mapLoop.processStack RPOrig.nextGreaterElement.resultLoop RPOrig.nextGreaterElement.resultLoop.findInMap RPRef.nextGreaterElement.mapLoop RPRef.nextGreaterElement.mapLoop.processStack RPRef.nextGreaterElement.resultLoop RPRef.nextGreaterElement.resultLoop.findInMap; rfl) | (delta RPOrig.nextGreaterElement RPRef.nextGreaterElement RPOrig.nextGreaterElement.mapLoop RPOrig.nextGreaterElement.mapLoop.processStack RPOrig.nextGreaterElement.resultLoop RPOrig.nextGreaterElement.resultLoop.findInMap RPRef.nextGreaterElement.mapLoop RPRef.nextGreaterElement.mapLoop.processStack RPRef.nextGreaterElement.resultLoop RPRef.nextGreaterElement.resultLoop.findInMap RPOrig.nextGreaterElement._unary RPOrig.nextGreaterElement.mapLoop._unary RPOrig.nextGreaterElement.mapLoop.processStack._unary RPOrig.nextGreaterElement.resultLoop._unary RPOrig.nextGreaterElement.resultLoop.findInMap._unary RPRef.nextGreaterElement.mapLoop._unary RPRef.nextGreaterElement.mapLoop.processStack._unary RPRef.nextGreaterElement.resultLoop._unary RPRef.nextGreaterElement.resultLoop.findInMap._unary; rfl) | (set_option smartUnfolding false in rfl))
    | (simp only [RPOrig.nextGreaterElement, RPRef.nextGreaterElement, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (delta RPOrig.nextGreaterElement RPRef.nextGreaterElement RPOrig.nextGreaterElement.mapLoop RPOrig.nextGreaterElement.mapLoop.processStack RPOrig.nextGreaterElement.resultLoop RPOrig.nextGreaterElement.resultLoop.findInMap RPRef.nextGreaterElement.mapLoop RPRef.nextGreaterElement.mapLoop.processStack RPRef.nextGreaterElement.resultLoop RPRef.nextGreaterElement.resultLoop.findInMap; rfl) | (delta RPOrig.nextGreaterElement RPRef.nextGreaterElement RPOrig.nextGreaterElement.mapLoop RPOrig.nextGreaterElement.mapLoop.processStack RPOrig.nextGreaterElement.resultLoop RPOrig.nextGreaterElement.resultLoop.findInMap RPRef.nextGreaterElement.mapLoop RPRef.nextGreaterElement.mapLoop.processStack RPRef.nextGreaterElement.resultLoop RPRef.nextGreaterElement.resultLoop.findInMap RPOrig.nextGreaterElement._unary RPOrig.nextGreaterElement.mapLoop._unary RPOrig.nextGreaterElement.mapLoop.processStack._unary RPOrig.nextGreaterElement.resultLoop._unary RPOrig.nextGreaterElement.resultLoop.findInMap._unary RPRef.nextGreaterElement.mapLoop._unary RPRef.nextGreaterElement.mapLoop.processStack._unary RPRef.nextGreaterElement.resultLoop._unary RPRef.nextGreaterElement.resultLoop.findInMap._unary; rfl) | (set_option smartUnfolding false in rfl))
    | (simp only [RPOrig.nextGreaterElement, RPRef.nextGreaterElement, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (delta RPOrig.nextGreaterElement RPRef.nextGreaterElement RPOrig.nextGreaterElement.mapLoop RPOrig.nextGreaterElement.mapLoop.processStack RPOrig.nextGreaterElement.resultLoop RPOrig.nextGreaterElement.resultLoop.findInMap RPRef.nextGreaterElement.mapLoop RPRef.nextGreaterElement.mapLoop.processStack RPRef.nextGreaterElement.resultLoop RPRef.nextGreaterElement.resultLoop.findInMap; rfl) | (delta RPOrig.nextGreaterElement RPRef.nextGreaterElement RPOrig.nextGreaterElement.mapLoop RPOrig.nextGreaterElement.mapLoop.processStack RPOrig.nextGreaterElement.resultLoop RPOrig.nextGreaterElement.resultLoop.findInMap RPRef.nextGreaterElement.mapLoop RPRef.nextGreaterElement.mapLoop.processStack RPRef.nextGreaterElement.resultLoop RPRef.nextGreaterElement.resultLoop.findInMap RPOrig.nextGreaterElement._unary RPOrig.nextGreaterElement.mapLoop._unary RPOrig.nextGreaterElement.mapLoop.processStack._unary RPOrig.nextGreaterElement.resultLoop._unary RPOrig.nextGreaterElement.resultLoop.findInMap._unary RPRef.nextGreaterElement.mapLoop._unary RPRef.nextGreaterElement.mapLoop.processStack._unary RPRef.nextGreaterElement.resultLoop._unary RPRef.nextGreaterElement.resultLoop.findInMap._unary; rfl) | (set_option smartUnfolding false in rfl))
    | (simp only [RPOrig.nextGreaterElement, RPRef.nextGreaterElement]) <;> (first | rfl | (delta RPOrig.nextGreaterElement RPRef.nextGreaterElement RPOrig.nextGreaterElement.mapLoop RPOrig.nextGreaterElement.mapLoop.processStack RPOrig.nextGreaterElement.resultLoop RPOrig.nextGreaterElement.resultLoop.findInMap RPRef.nextGreaterElement.mapLoop RPRef.nextGreaterElement.mapLoop.processStack RPRef.nextGreaterElement.resultLoop RPRef.nextGreaterElement.resultLoop.findInMap; rfl) | (delta RPOrig.nextGreaterElement RPRef.nextGreaterElement RPOrig.nextGreaterElement.mapLoop RPOrig.nextGreaterElement.mapLoop.processStack RPOrig.nextGreaterElement.resultLoop RPOrig.nextGreaterElement.resultLoop.findInMap RPRef.nextGreaterElement.mapLoop RPRef.nextGreaterElement.mapLoop.processStack RPRef.nextGreaterElement.resultLoop RPRef.nextGreaterElement.resultLoop.findInMap RPOrig.nextGreaterElement._unary RPOrig.nextGreaterElement.mapLoop._unary RPOrig.nextGreaterElement.mapLoop.processStack._unary RPOrig.nextGreaterElement.resultLoop._unary RPOrig.nextGreaterElement.resultLoop.findInMap._unary RPRef.nextGreaterElement.mapLoop._unary RPRef.nextGreaterElement.mapLoop.processStack._unary RPRef.nextGreaterElement.resultLoop._unary RPRef.nextGreaterElement.resultLoop.findInMap._unary; rfl) | (set_option smartUnfolding false in rfl))

theorem rp_equiv_simp (nums1 : List Int) (nums2 : List Int) (h_precond : nextGreaterElement_precond (nums1) (nums2)) :
    RPOrig.nextGreaterElement nums1 nums2 h_precond = RPRef.nextGreaterElement nums1 nums2 h_precond := by
  first
    | (simp [RPOrig.nextGreaterElement, RPRef.nextGreaterElement, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (delta RPOrig.nextGreaterElement RPRef.nextGreaterElement RPOrig.nextGreaterElement.mapLoop RPOrig.nextGreaterElement.mapLoop.processStack RPOrig.nextGreaterElement.resultLoop RPOrig.nextGreaterElement.resultLoop.findInMap RPRef.nextGreaterElement.mapLoop RPRef.nextGreaterElement.mapLoop.processStack RPRef.nextGreaterElement.resultLoop RPRef.nextGreaterElement.resultLoop.findInMap; rfl) | (delta RPOrig.nextGreaterElement RPRef.nextGreaterElement RPOrig.nextGreaterElement.mapLoop RPOrig.nextGreaterElement.mapLoop.processStack RPOrig.nextGreaterElement.resultLoop RPOrig.nextGreaterElement.resultLoop.findInMap RPRef.nextGreaterElement.mapLoop RPRef.nextGreaterElement.mapLoop.processStack RPRef.nextGreaterElement.resultLoop RPRef.nextGreaterElement.resultLoop.findInMap RPOrig.nextGreaterElement._unary RPOrig.nextGreaterElement.mapLoop._unary RPOrig.nextGreaterElement.mapLoop.processStack._unary RPOrig.nextGreaterElement.resultLoop._unary RPOrig.nextGreaterElement.resultLoop.findInMap._unary RPRef.nextGreaterElement.mapLoop._unary RPRef.nextGreaterElement.mapLoop.processStack._unary RPRef.nextGreaterElement.resultLoop._unary RPRef.nextGreaterElement.resultLoop.findInMap._unary; rfl) | (set_option smartUnfolding false in rfl))
    | (simp [RPOrig.nextGreaterElement, RPRef.nextGreaterElement, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (delta RPOrig.nextGreaterElement RPRef.nextGreaterElement RPOrig.nextGreaterElement.mapLoop RPOrig.nextGreaterElement.mapLoop.processStack RPOrig.nextGreaterElement.resultLoop RPOrig.nextGreaterElement.resultLoop.findInMap RPRef.nextGreaterElement.mapLoop RPRef.nextGreaterElement.mapLoop.processStack RPRef.nextGreaterElement.resultLoop RPRef.nextGreaterElement.resultLoop.findInMap; rfl) | (delta RPOrig.nextGreaterElement RPRef.nextGreaterElement RPOrig.nextGreaterElement.mapLoop RPOrig.nextGreaterElement.mapLoop.processStack RPOrig.nextGreaterElement.resultLoop RPOrig.nextGreaterElement.resultLoop.findInMap RPRef.nextGreaterElement.mapLoop RPRef.nextGreaterElement.mapLoop.processStack RPRef.nextGreaterElement.resultLoop RPRef.nextGreaterElement.resultLoop.findInMap RPOrig.nextGreaterElement._unary RPOrig.nextGreaterElement.mapLoop._unary RPOrig.nextGreaterElement.mapLoop.processStack._unary RPOrig.nextGreaterElement.resultLoop._unary RPOrig.nextGreaterElement.resultLoop.findInMap._unary RPRef.nextGreaterElement.mapLoop._unary RPRef.nextGreaterElement.mapLoop.processStack._unary RPRef.nextGreaterElement.resultLoop._unary RPRef.nextGreaterElement.resultLoop.findInMap._unary; rfl) | (set_option smartUnfolding false in rfl))
    | (simp [RPOrig.nextGreaterElement, RPRef.nextGreaterElement, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (delta RPOrig.nextGreaterElement RPRef.nextGreaterElement RPOrig.nextGreaterElement.mapLoop RPOrig.nextGreaterElement.mapLoop.processStack RPOrig.nextGreaterElement.resultLoop RPOrig.nextGreaterElement.resultLoop.findInMap RPRef.nextGreaterElement.mapLoop RPRef.nextGreaterElement.mapLoop.processStack RPRef.nextGreaterElement.resultLoop RPRef.nextGreaterElement.resultLoop.findInMap; rfl) | (delta RPOrig.nextGreaterElement RPRef.nextGreaterElement RPOrig.nextGreaterElement.mapLoop RPOrig.nextGreaterElement.mapLoop.processStack RPOrig.nextGreaterElement.resultLoop RPOrig.nextGreaterElement.resultLoop.findInMap RPRef.nextGreaterElement.mapLoop RPRef.nextGreaterElement.mapLoop.processStack RPRef.nextGreaterElement.resultLoop RPRef.nextGreaterElement.resultLoop.findInMap RPOrig.nextGreaterElement._unary RPOrig.nextGreaterElement.mapLoop._unary RPOrig.nextGreaterElement.mapLoop.processStack._unary RPOrig.nextGreaterElement.resultLoop._unary RPOrig.nextGreaterElement.resultLoop.findInMap._unary RPRef.nextGreaterElement.mapLoop._unary RPRef.nextGreaterElement.mapLoop.processStack._unary RPRef.nextGreaterElement.resultLoop._unary RPRef.nextGreaterElement.resultLoop.findInMap._unary; rfl) | (set_option smartUnfolding false in rfl))
    | (simp [RPOrig.nextGreaterElement, RPRef.nextGreaterElement]) <;> (first | rfl | (delta RPOrig.nextGreaterElement RPRef.nextGreaterElement RPOrig.nextGreaterElement.mapLoop RPOrig.nextGreaterElement.mapLoop.processStack RPOrig.nextGreaterElement.resultLoop RPOrig.nextGreaterElement.resultLoop.findInMap RPRef.nextGreaterElement.mapLoop RPRef.nextGreaterElement.mapLoop.processStack RPRef.nextGreaterElement.resultLoop RPRef.nextGreaterElement.resultLoop.findInMap; rfl) | (delta RPOrig.nextGreaterElement RPRef.nextGreaterElement RPOrig.nextGreaterElement.mapLoop RPOrig.nextGreaterElement.mapLoop.processStack RPOrig.nextGreaterElement.resultLoop RPOrig.nextGreaterElement.resultLoop.findInMap RPRef.nextGreaterElement.mapLoop RPRef.nextGreaterElement.mapLoop.processStack RPRef.nextGreaterElement.resultLoop RPRef.nextGreaterElement.resultLoop.findInMap RPOrig.nextGreaterElement._unary RPOrig.nextGreaterElement.mapLoop._unary RPOrig.nextGreaterElement.mapLoop.processStack._unary RPOrig.nextGreaterElement.resultLoop._unary RPOrig.nextGreaterElement.resultLoop.findInMap._unary RPRef.nextGreaterElement.mapLoop._unary RPRef.nextGreaterElement.mapLoop.processStack._unary RPRef.nextGreaterElement.resultLoop._unary RPRef.nextGreaterElement.resultLoop.findInMap._unary; rfl) | (set_option smartUnfolding false in rfl))

theorem rp_equiv_ac_rfl (nums1 : List Int) (nums2 : List Int) (h_precond : nextGreaterElement_precond (nums1) (nums2)) :
    RPOrig.nextGreaterElement nums1 nums2 h_precond = RPRef.nextGreaterElement nums1 nums2 h_precond := by
  (try simp only [RPOrig.nextGreaterElement, RPRef.nextGreaterElement]) <;> (try ac_nf) <;> (first | rfl | (delta RPOrig.nextGreaterElement RPRef.nextGreaterElement RPOrig.nextGreaterElement.mapLoop RPOrig.nextGreaterElement.mapLoop.processStack RPOrig.nextGreaterElement.resultLoop RPOrig.nextGreaterElement.resultLoop.findInMap RPRef.nextGreaterElement.mapLoop RPRef.nextGreaterElement.mapLoop.processStack RPRef.nextGreaterElement.resultLoop RPRef.nextGreaterElement.resultLoop.findInMap; rfl) | (delta RPOrig.nextGreaterElement RPRef.nextGreaterElement RPOrig.nextGreaterElement.mapLoop RPOrig.nextGreaterElement.mapLoop.processStack RPOrig.nextGreaterElement.resultLoop RPOrig.nextGreaterElement.resultLoop.findInMap RPRef.nextGreaterElement.mapLoop RPRef.nextGreaterElement.mapLoop.processStack RPRef.nextGreaterElement.resultLoop RPRef.nextGreaterElement.resultLoop.findInMap RPOrig.nextGreaterElement._unary RPOrig.nextGreaterElement.mapLoop._unary RPOrig.nextGreaterElement.mapLoop.processStack._unary RPOrig.nextGreaterElement.resultLoop._unary RPOrig.nextGreaterElement.resultLoop.findInMap._unary RPRef.nextGreaterElement.mapLoop._unary RPRef.nextGreaterElement.mapLoop.processStack._unary RPRef.nextGreaterElement.resultLoop._unary RPRef.nextGreaterElement.resultLoop.findInMap._unary; rfl) | (set_option smartUnfolding false in rfl))
