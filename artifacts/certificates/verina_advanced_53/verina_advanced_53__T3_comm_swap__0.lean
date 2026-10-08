-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def minimumRightShifts_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  List.Nodup nums
  -- !benchmark @end precond



namespace RPOrig

def minimumRightShifts (nums : List Int) (h_precond : minimumRightShifts_precond (nums)) : Int :=
  let n := nums.length
  -- base cases: empty or single element list is already sorted
  if n <= 1 then 0 else

  -- local helper function to check if a list is sorted in ascending order
  let rec isSortedAux (l : List Int) : Bool :=
    match l with
    | [] => true       -- empty list is sorted
    | [_] => true      -- single element list is sorted
    | x :: y :: xs => if x <= y then isSortedAux (y :: xs) else false -- check pairwise

  -- check if the input list is already sorted
  if isSortedAux nums then 0 else

  -- local helper function to perform a single right shift
  -- assume the list `l` is non-empty based on the initial n > 1 check
  let rightShiftOnce (l : List Int) : List Int :=
     match l.reverse with
     | [] => [] -- should not happen for n > 1
     | last :: revInit => last :: revInit.reverse -- `last` is the original last element

  -- recursive function to check subsequent shifts
  -- `shifts_count` is the number of shifts already performed to get `current_list`
  -- we are checking if `current_list` is sorted
  let rec checkShifts (shifts_count : Nat) (current_list : List Int) : Int :=
    -- base case: stop recursion if we've checked n-1 shifts (count goes from 1 to n)
    -- the original list (0 shifts) has already been checked
    if shifts_count >= n then -1
    else
      -- check if the current state is sorted
      if isSortedAux current_list then
        (shifts_count : Int) -- found it after 'shifts_count' shifts
      else
        -- recursion: increment shift count, apply next shift
        checkShifts (shifts_count + 1) (rightShiftOnce current_list)
  -- specify the decreasing measure for the termination checker: n - shifts_count
  termination_by n - shifts_count

  -- start the checking process by performing the first shift and checking subsequent states
  -- the initial list (0 shifts) hass already been checked and is not sorted
  checkShifts 1 (rightShiftOnce nums) -- start checking from the state after 1 shift
end RPOrig

namespace RPRef

def minimumRightShifts (nums : List Int) (h_precond : minimumRightShifts_precond (nums)) : Int :=
  let n := nums.length
  -- base cases: empty or single element list is already sorted
  if n <= 1 then 0 else

  -- local helper function to check if a list is sorted in ascending order
  let rec isSortedAux (l : List Int) : Bool :=
    match l with
    | [] => true       -- empty list is sorted
    | [_] => true      -- single element list is sorted
    | x :: y :: xs => if x <= y then isSortedAux (y :: xs) else false -- check pairwise

  -- check if the input list is already sorted
  if isSortedAux nums then 0 else

  -- local helper function to perform a single right shift
  -- assume the list `l` is non-empty based on the initial n > 1 check
  let rightShiftOnce (l : List Int) : List Int :=
     match l.reverse with
     | [] => [] -- should not happen for n > 1
     | last :: revInit => last :: revInit.reverse -- `last` is the original last element

  -- recursive function to check subsequent shifts
  -- `shifts_count` is the number of shifts already performed to get `current_list`
  -- we are checking if `current_list` is sorted
  let rec checkShifts (shifts_count : Nat) (current_list : List Int) : Int :=
    -- base case: stop recursion if we've checked n-1 shifts (count goes from 1 to n)
    -- the original list (0 shifts) has already been checked
    if shifts_count >= n then -1
    else
      -- check if the current state is sorted
      if isSortedAux current_list then
        (shifts_count : Int) -- found it after 'shifts_count' shifts
      else
        -- recursion: increment shift count, apply next shift
        checkShifts (1 + shifts_count) (rightShiftOnce current_list)
  -- specify the decreasing measure for the termination checker: n - shifts_count
  termination_by n - shifts_count

  -- start the checking process by performing the first shift and checking subsequent states
  -- the initial list (0 shifts) hass already been checked and is not sorted
  checkShifts 1 (rightShiftOnce nums) -- start checking from the state after 1 shift
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (nums : List Int) (h_precond : minimumRightShifts_precond (nums)) :
    RPOrig.minimumRightShifts nums h_precond = RPRef.minimumRightShifts nums h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (nums : List Int) (h_precond : minimumRightShifts_precond (nums)) :
    RPOrig.minimumRightShifts nums h_precond = RPRef.minimumRightShifts nums h_precond := rfl

theorem rp_equiv_delta_rfl (nums : List Int) (h_precond : minimumRightShifts_precond (nums)) :
    RPOrig.minimumRightShifts nums h_precond = RPRef.minimumRightShifts nums h_precond := by
  delta RPOrig.minimumRightShifts RPRef.minimumRightShifts RPOrig.minimumRightShifts.isSortedAux RPOrig.minimumRightShifts.checkShifts RPRef.minimumRightShifts.isSortedAux RPRef.minimumRightShifts.checkShifts
  rfl

theorem rp_equiv_simp_only (nums : List Int) (h_precond : minimumRightShifts_precond (nums)) :
    RPOrig.minimumRightShifts nums h_precond = RPRef.minimumRightShifts nums h_precond := by
  first
    | (simp only [RPOrig.minimumRightShifts, RPRef.minimumRightShifts, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.minimumRightShifts RPRef.minimumRightShifts RPOrig.minimumRightShifts.isSortedAux RPOrig.minimumRightShifts.checkShifts RPRef.minimumRightShifts.isSortedAux RPRef.minimumRightShifts.checkShifts; rfl))
    | (simp only [RPOrig.minimumRightShifts, RPRef.minimumRightShifts, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.minimumRightShifts RPRef.minimumRightShifts RPOrig.minimumRightShifts.isSortedAux RPOrig.minimumRightShifts.checkShifts RPRef.minimumRightShifts.isSortedAux RPRef.minimumRightShifts.checkShifts; rfl))
    | (simp only [RPOrig.minimumRightShifts, RPRef.minimumRightShifts, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.minimumRightShifts RPRef.minimumRightShifts RPOrig.minimumRightShifts.isSortedAux RPOrig.minimumRightShifts.checkShifts RPRef.minimumRightShifts.isSortedAux RPRef.minimumRightShifts.checkShifts; rfl))
    | (simp only [RPOrig.minimumRightShifts, RPRef.minimumRightShifts]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.minimumRightShifts RPRef.minimumRightShifts RPOrig.minimumRightShifts.isSortedAux RPOrig.minimumRightShifts.checkShifts RPRef.minimumRightShifts.isSortedAux RPRef.minimumRightShifts.checkShifts; rfl))

theorem rp_equiv_simp (nums : List Int) (h_precond : minimumRightShifts_precond (nums)) :
    RPOrig.minimumRightShifts nums h_precond = RPRef.minimumRightShifts nums h_precond := by
  first
    | (simp [RPOrig.minimumRightShifts, RPRef.minimumRightShifts, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.minimumRightShifts RPRef.minimumRightShifts RPOrig.minimumRightShifts.isSortedAux RPOrig.minimumRightShifts.checkShifts RPRef.minimumRightShifts.isSortedAux RPRef.minimumRightShifts.checkShifts; rfl))
    | (simp [RPOrig.minimumRightShifts, RPRef.minimumRightShifts, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.minimumRightShifts RPRef.minimumRightShifts RPOrig.minimumRightShifts.isSortedAux RPOrig.minimumRightShifts.checkShifts RPRef.minimumRightShifts.isSortedAux RPRef.minimumRightShifts.checkShifts; rfl))
    | (simp [RPOrig.minimumRightShifts, RPRef.minimumRightShifts, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.minimumRightShifts RPRef.minimumRightShifts RPOrig.minimumRightShifts.isSortedAux RPOrig.minimumRightShifts.checkShifts RPRef.minimumRightShifts.isSortedAux RPRef.minimumRightShifts.checkShifts; rfl))
    | (simp [RPOrig.minimumRightShifts, RPRef.minimumRightShifts]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.minimumRightShifts RPRef.minimumRightShifts RPOrig.minimumRightShifts.isSortedAux RPOrig.minimumRightShifts.checkShifts RPRef.minimumRightShifts.isSortedAux RPRef.minimumRightShifts.checkShifts; rfl))

theorem rp_equiv_ac_rfl (nums : List Int) (h_precond : minimumRightShifts_precond (nums)) :
    RPOrig.minimumRightShifts nums h_precond = RPRef.minimumRightShifts nums h_precond := by
  (try simp only [RPOrig.minimumRightShifts, RPRef.minimumRightShifts]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.minimumRightShifts RPRef.minimumRightShifts RPOrig.minimumRightShifts.isSortedAux RPOrig.minimumRightShifts.checkShifts RPRef.minimumRightShifts.isSortedAux RPRef.minimumRightShifts.checkShifts; rfl))
