-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def majorityElement_precond (xs : List Nat) : Prop :=
  -- !benchmark @start precond
  xs.length > 0 ∧ xs.any (fun x => xs.count x > xs.length / 2)
  -- !benchmark @end precond



namespace RPOrig

def majorityElement (xs : List Nat) (h_precond : majorityElement_precond (xs)) : Nat :=
  let rec countOccurrences (target : Nat) (lst : List Nat) : Nat :=
    match lst with
    | [] => 0
    | y :: ys =>
      if y = target then 1 + countOccurrences target ys
      else countOccurrences target ys

  let rec findCandidate (lst : List Nat) (candidate : Option Nat) (count : Nat) : Nat :=
    match lst with
    | [] =>
      match candidate with
      | some c => c
      | none => 0 -- unreachable since we assume majority element exists
    | x :: xs =>
      match candidate with
      | some c =>
        if x = c then
          findCandidate xs (some c) (count + 1)
        else if count = 0 then
          findCandidate xs (some x) 1
        else
          findCandidate xs (some c) (count - 1)
      | none =>
        findCandidate xs (some x) 1

  let cand := findCandidate xs none 0
  cand
end RPOrig

namespace RPRef

def majorityElement (xs : List Nat) (h_precond : majorityElement_precond (xs)) : Nat :=
  let rec countOccurrences (target : Nat) (lst : List Nat) : Nat :=
    match lst with
    | [] => 0
    | y :: ys =>
      if y = target then 1 + countOccurrences target ys
      else countOccurrences target ys

  let rec findCandidate (lst : List Nat) (candidate : Option Nat) (count : Nat) : Nat :=
    match lst with
    | [] =>
      match candidate with
      | some c => c
      | none => 0 -- unreachable since we assume majority element exists
    | x :: xs =>
      match candidate with
      | some c =>
        if x = c then
          findCandidate xs (some c) (1 + count)
        else if count = 0 then
          findCandidate xs (some x) 1
        else
          findCandidate xs (some c) (count - 1)
      | none =>
        findCandidate xs (some x) 1

  let cand := findCandidate xs none 0
  cand
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (xs : List Nat) (h_precond : majorityElement_precond (xs)) :
    RPOrig.majorityElement xs h_precond = RPRef.majorityElement xs h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (xs : List Nat) (h_precond : majorityElement_precond (xs)) :
    RPOrig.majorityElement xs h_precond = RPRef.majorityElement xs h_precond := rfl

theorem rp_equiv_delta_rfl (xs : List Nat) (h_precond : majorityElement_precond (xs)) :
    RPOrig.majorityElement xs h_precond = RPRef.majorityElement xs h_precond := by
  delta RPOrig.majorityElement RPRef.majorityElement RPOrig.majorityElement.countOccurrences RPOrig.majorityElement.findCandidate RPRef.majorityElement.countOccurrences RPRef.majorityElement.findCandidate
  rfl

theorem rp_equiv_simp_only (xs : List Nat) (h_precond : majorityElement_precond (xs)) :
    RPOrig.majorityElement xs h_precond = RPRef.majorityElement xs h_precond := by
  first
    | (simp only [RPOrig.majorityElement, RPRef.majorityElement, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.majorityElement RPRef.majorityElement RPOrig.majorityElement.countOccurrences RPOrig.majorityElement.findCandidate RPRef.majorityElement.countOccurrences RPRef.majorityElement.findCandidate; rfl))
    | (simp only [RPOrig.majorityElement, RPRef.majorityElement, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.majorityElement RPRef.majorityElement RPOrig.majorityElement.countOccurrences RPOrig.majorityElement.findCandidate RPRef.majorityElement.countOccurrences RPRef.majorityElement.findCandidate; rfl))
    | (simp only [RPOrig.majorityElement, RPRef.majorityElement, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.majorityElement RPRef.majorityElement RPOrig.majorityElement.countOccurrences RPOrig.majorityElement.findCandidate RPRef.majorityElement.countOccurrences RPRef.majorityElement.findCandidate; rfl))
    | (simp only [RPOrig.majorityElement, RPRef.majorityElement]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.majorityElement RPRef.majorityElement RPOrig.majorityElement.countOccurrences RPOrig.majorityElement.findCandidate RPRef.majorityElement.countOccurrences RPRef.majorityElement.findCandidate; rfl))

theorem rp_equiv_simp (xs : List Nat) (h_precond : majorityElement_precond (xs)) :
    RPOrig.majorityElement xs h_precond = RPRef.majorityElement xs h_precond := by
  first
    | (simp [RPOrig.majorityElement, RPRef.majorityElement, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.majorityElement RPRef.majorityElement RPOrig.majorityElement.countOccurrences RPOrig.majorityElement.findCandidate RPRef.majorityElement.countOccurrences RPRef.majorityElement.findCandidate; rfl))
    | (simp [RPOrig.majorityElement, RPRef.majorityElement, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.majorityElement RPRef.majorityElement RPOrig.majorityElement.countOccurrences RPOrig.majorityElement.findCandidate RPRef.majorityElement.countOccurrences RPRef.majorityElement.findCandidate; rfl))
    | (simp [RPOrig.majorityElement, RPRef.majorityElement, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.majorityElement RPRef.majorityElement RPOrig.majorityElement.countOccurrences RPOrig.majorityElement.findCandidate RPRef.majorityElement.countOccurrences RPRef.majorityElement.findCandidate; rfl))
    | (simp [RPOrig.majorityElement, RPRef.majorityElement]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.majorityElement RPRef.majorityElement RPOrig.majorityElement.countOccurrences RPOrig.majorityElement.findCandidate RPRef.majorityElement.countOccurrences RPRef.majorityElement.findCandidate; rfl))

theorem rp_equiv_ac_rfl (xs : List Nat) (h_precond : majorityElement_precond (xs)) :
    RPOrig.majorityElement xs h_precond = RPRef.majorityElement xs h_precond := by
  (try simp only [RPOrig.majorityElement, RPRef.majorityElement]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.majorityElement RPRef.majorityElement RPOrig.majorityElement.countOccurrences RPOrig.majorityElement.findCandidate RPRef.majorityElement.countOccurrences RPRef.majorityElement.findCandidate; rfl))
