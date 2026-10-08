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
private def majorityElement__rp_helper_4bdb9cde (xs : List Nat) (h_precond : majorityElement_precond (xs)) : Nat :=
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

def majorityElement (xs : List Nat) (h_precond : majorityElement_precond (xs)) : Nat :=
  majorityElement__rp_helper_4bdb9cde xs h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (xs : List Nat) (h_precond : majorityElement_precond (xs)) :
    RPOrig.majorityElement xs h_precond = RPRef.majorityElement xs h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (xs : List Nat) (h_precond : majorityElement_precond (xs)) :
    RPOrig.majorityElement xs h_precond = RPRef.majorityElement xs h_precond := rfl

theorem rp_equiv_delta_rfl (xs : List Nat) (h_precond : majorityElement_precond (xs)) :
    RPOrig.majorityElement xs h_precond = RPRef.majorityElement xs h_precond := by
  delta RPOrig.majorityElement RPRef.majorityElement RPRef.majorityElement__rp_helper_4bdb9cde RPOrig.majorityElement.countOccurrences RPOrig.majorityElement.findCandidate RPRef.majorityElement__rp_helper_4bdb9cde.countOccurrences RPRef.majorityElement__rp_helper_4bdb9cde.findCandidate
  rfl

theorem rp_equiv_simp_only (xs : List Nat) (h_precond : majorityElement_precond (xs)) :
    RPOrig.majorityElement xs h_precond = RPRef.majorityElement xs h_precond := by
  (simp only [RPOrig.majorityElement, RPRef.majorityElement, RPRef.majorityElement__rp_helper_4bdb9cde]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.majorityElement RPRef.majorityElement RPRef.majorityElement__rp_helper_4bdb9cde RPOrig.majorityElement.countOccurrences RPOrig.majorityElement.findCandidate RPRef.majorityElement__rp_helper_4bdb9cde.countOccurrences RPRef.majorityElement__rp_helper_4bdb9cde.findCandidate; rfl))

theorem rp_equiv_simp (xs : List Nat) (h_precond : majorityElement_precond (xs)) :
    RPOrig.majorityElement xs h_precond = RPRef.majorityElement xs h_precond := by
  (simp [RPOrig.majorityElement, RPRef.majorityElement, RPRef.majorityElement__rp_helper_4bdb9cde]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.majorityElement RPRef.majorityElement RPRef.majorityElement__rp_helper_4bdb9cde RPOrig.majorityElement.countOccurrences RPOrig.majorityElement.findCandidate RPRef.majorityElement__rp_helper_4bdb9cde.countOccurrences RPRef.majorityElement__rp_helper_4bdb9cde.findCandidate; rfl))
