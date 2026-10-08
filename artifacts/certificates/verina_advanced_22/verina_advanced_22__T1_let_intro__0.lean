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
  let __rp_tmp_72d87e4f : Bool :=
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
  __rp_tmp_72d87e4f
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
  (simp only [RPOrig.isPeakValley, RPRef.isPeakValley]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPeakValley RPRef.isPeakValley RPOrig.isPeakValley.aux RPRef.isPeakValley.aux; rfl))

theorem rp_equiv_simp (lst : List Int) (h_precond : isPeakValley_precond (lst)) :
    RPOrig.isPeakValley lst h_precond = RPRef.isPeakValley lst h_precond := by
  (simp [RPOrig.isPeakValley, RPRef.isPeakValley]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPeakValley RPRef.isPeakValley RPOrig.isPeakValley.aux RPRef.isPeakValley.aux; rfl))
