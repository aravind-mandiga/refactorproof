-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def isPeakValley_precond (lst : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def isPeakValley (lst : List Int) (h_precond : isPeakValley_precond (lst)) : Bool :=
  let rec aux (l : List Int) (increasing : Bool) (startedDecreasing : Bool) : Bool :=
    match l with
    | x :: y :: rest =>
      if x < y then
        if startedDecreasing then false
        else aux (y :: rest) true startedDecreasing
      else if x > y then
        if increasing then aux (y :: rest) increasing true
        else false
      else false
    | _ => increasing && startedDecreasing
  aux lst false false
end RPOrig

namespace RPRef

def isPeakValley (lst : List Int) (h_precond : isPeakValley_precond (lst)) : Bool :=
  let rec aux (l : List Int) (increasing : Bool) (startedDecreasing : Bool) : Bool :=
    match l with
    | x :: y :: rest =>
      if x < y then
        if startedDecreasing then false
        else aux (y :: rest) true startedDecreasing
      else if x > y then
        if increasing then aux (y :: rest) increasing true
        else false
      else false
    | _ => startedDecreasing && increasing
  aux lst false false
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (lst : List Int) (h_precond : isPeakValley_precond (lst)) :
    RPOrig.isPeakValley lst h_precond = RPRef.isPeakValley lst h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (lst : List Int) (h_precond : isPeakValley_precond (lst)) :
    RPOrig.isPeakValley lst h_precond = RPRef.isPeakValley lst h_precond := rfl

theorem rp_equiv_delta_rfl (lst : List Int) (h_precond : isPeakValley_precond (lst)) :
    RPOrig.isPeakValley lst h_precond = RPRef.isPeakValley lst h_precond := by
  delta RPOrig.isPeakValley RPRef.isPeakValley RPOrig.isPeakValley.aux RPRef.isPeakValley.aux
  rfl

theorem rp_equiv_simp_only (lst : List Int) (h_precond : isPeakValley_precond (lst)) :
    RPOrig.isPeakValley lst h_precond = RPRef.isPeakValley lst h_precond := by
  first
    | (simp only [RPOrig.isPeakValley, RPRef.isPeakValley, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPeakValley RPRef.isPeakValley RPOrig.isPeakValley.aux RPRef.isPeakValley.aux; rfl))
    | (simp only [RPOrig.isPeakValley, RPRef.isPeakValley, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPeakValley RPRef.isPeakValley RPOrig.isPeakValley.aux RPRef.isPeakValley.aux; rfl))
    | (simp only [RPOrig.isPeakValley, RPRef.isPeakValley, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPeakValley RPRef.isPeakValley RPOrig.isPeakValley.aux RPRef.isPeakValley.aux; rfl))
    | (simp only [RPOrig.isPeakValley, RPRef.isPeakValley]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPeakValley RPRef.isPeakValley RPOrig.isPeakValley.aux RPRef.isPeakValley.aux; rfl))

theorem rp_equiv_simp (lst : List Int) (h_precond : isPeakValley_precond (lst)) :
    RPOrig.isPeakValley lst h_precond = RPRef.isPeakValley lst h_precond := by
  first
    | (simp [RPOrig.isPeakValley, RPRef.isPeakValley, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPeakValley RPRef.isPeakValley RPOrig.isPeakValley.aux RPRef.isPeakValley.aux; rfl))
    | (simp [RPOrig.isPeakValley, RPRef.isPeakValley, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPeakValley RPRef.isPeakValley RPOrig.isPeakValley.aux RPRef.isPeakValley.aux; rfl))
    | (simp [RPOrig.isPeakValley, RPRef.isPeakValley, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPeakValley RPRef.isPeakValley RPOrig.isPeakValley.aux RPRef.isPeakValley.aux; rfl))
    | (simp [RPOrig.isPeakValley, RPRef.isPeakValley]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPeakValley RPRef.isPeakValley RPOrig.isPeakValley.aux RPRef.isPeakValley.aux; rfl))

theorem rp_equiv_ac_rfl (lst : List Int) (h_precond : isPeakValley_precond (lst)) :
    RPOrig.isPeakValley lst h_precond = RPRef.isPeakValley lst h_precond := by
  (try simp only [RPOrig.isPeakValley, RPRef.isPeakValley]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPeakValley RPRef.isPeakValley RPOrig.isPeakValley.aux RPRef.isPeakValley.aux; rfl))
