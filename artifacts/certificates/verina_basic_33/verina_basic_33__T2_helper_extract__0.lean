-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def smallestMissingNumber_precond (s : List Nat) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· ≤ ·) s
  -- !benchmark @end precond


namespace RPOrig

def smallestMissingNumber (s : List Nat) (h_precond : smallestMissingNumber_precond (s)) : Nat :=
  let rec findMissing (v : Nat) (l : List Nat) : Nat :=
    match l with
    | [] => v
    | x :: xs =>
      if x > v then v
      else if x = v then findMissing (v + 1) xs
      else findMissing v xs
  findMissing 0 s
end RPOrig

namespace RPRef
private def smallestMissingNumber__rp_helper_f9109aa0 (s : List Nat) (h_precond : smallestMissingNumber_precond (s)) : Nat :=
  let rec findMissing (v : Nat) (l : List Nat) : Nat :=
    match l with
    | [] => v
    | x :: xs =>
      if x > v then v
      else if x = v then findMissing (v + 1) xs
      else findMissing v xs
  findMissing 0 s

def smallestMissingNumber (s : List Nat) (h_precond : smallestMissingNumber_precond (s)) : Nat :=
  smallestMissingNumber__rp_helper_f9109aa0 s h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (s : List Nat) (h_precond : smallestMissingNumber_precond (s)) :
    RPOrig.smallestMissingNumber s h_precond = RPRef.smallestMissingNumber s h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (s : List Nat) (h_precond : smallestMissingNumber_precond (s)) :
    RPOrig.smallestMissingNumber s h_precond = RPRef.smallestMissingNumber s h_precond := rfl

theorem rp_equiv_delta_rfl (s : List Nat) (h_precond : smallestMissingNumber_precond (s)) :
    RPOrig.smallestMissingNumber s h_precond = RPRef.smallestMissingNumber s h_precond := by
  delta RPOrig.smallestMissingNumber RPRef.smallestMissingNumber RPRef.smallestMissingNumber__rp_helper_f9109aa0 RPOrig.smallestMissingNumber.findMissing RPRef.smallestMissingNumber__rp_helper_f9109aa0.findMissing
  rfl

theorem rp_equiv_simp_only (s : List Nat) (h_precond : smallestMissingNumber_precond (s)) :
    RPOrig.smallestMissingNumber s h_precond = RPRef.smallestMissingNumber s h_precond := by
  (simp only [RPOrig.smallestMissingNumber, RPRef.smallestMissingNumber, RPRef.smallestMissingNumber__rp_helper_f9109aa0]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.smallestMissingNumber RPRef.smallestMissingNumber RPRef.smallestMissingNumber__rp_helper_f9109aa0 RPOrig.smallestMissingNumber.findMissing RPRef.smallestMissingNumber__rp_helper_f9109aa0.findMissing; rfl))

theorem rp_equiv_simp (s : List Nat) (h_precond : smallestMissingNumber_precond (s)) :
    RPOrig.smallestMissingNumber s h_precond = RPRef.smallestMissingNumber s h_precond := by
  (simp [RPOrig.smallestMissingNumber, RPRef.smallestMissingNumber, RPRef.smallestMissingNumber__rp_helper_f9109aa0]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.smallestMissingNumber RPRef.smallestMissingNumber RPRef.smallestMissingNumber__rp_helper_f9109aa0 RPOrig.smallestMissingNumber.findMissing RPRef.smallestMissingNumber__rp_helper_f9109aa0.findMissing; rfl))
