-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def partitionEvensOdds_precond (nums : List Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def partitionEvensOdds (nums : List Nat) (h_precond : partitionEvensOdds_precond (nums)) : (List Nat × List Nat) :=
  let rec helper (nums : List Nat) : (List Nat × List Nat) :=
    match nums with
    | [] => ([], [])
    | x :: xs =>
      let (evens, odds) := helper xs
      if x % 2 == 0 then (x :: evens, odds)
      else (evens, x :: odds)
  helper nums
end RPOrig

namespace RPRef

def partitionEvensOdds (nums : List Nat) (h_precond : partitionEvensOdds_precond (nums)) : (List Nat × List Nat) :=
  let __rp_tmp_50305125 : (List Nat × List Nat) :=
    let rec helper (nums : List Nat) : (List Nat × List Nat) :=
      match nums with
      | [] => ([], [])
      | x :: xs =>
        let (evens, odds) := helper xs
        if x % 2 == 0 then (x :: evens, odds)
        else (evens, x :: odds)
    helper nums
  __rp_tmp_50305125
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (nums : List Nat) (h_precond : partitionEvensOdds_precond (nums)) :
    RPOrig.partitionEvensOdds nums h_precond = RPRef.partitionEvensOdds nums h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (nums : List Nat) (h_precond : partitionEvensOdds_precond (nums)) :
    RPOrig.partitionEvensOdds nums h_precond = RPRef.partitionEvensOdds nums h_precond := rfl

theorem rp_equiv_delta_rfl (nums : List Nat) (h_precond : partitionEvensOdds_precond (nums)) :
    RPOrig.partitionEvensOdds nums h_precond = RPRef.partitionEvensOdds nums h_precond := by
  delta RPOrig.partitionEvensOdds RPRef.partitionEvensOdds RPOrig.partitionEvensOdds.helper RPRef.partitionEvensOdds.helper
  rfl

theorem rp_equiv_simp_only (nums : List Nat) (h_precond : partitionEvensOdds_precond (nums)) :
    RPOrig.partitionEvensOdds nums h_precond = RPRef.partitionEvensOdds nums h_precond := by
  (simp only [RPOrig.partitionEvensOdds, RPRef.partitionEvensOdds]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.partitionEvensOdds RPRef.partitionEvensOdds RPOrig.partitionEvensOdds.helper RPRef.partitionEvensOdds.helper; rfl))

theorem rp_equiv_simp (nums : List Nat) (h_precond : partitionEvensOdds_precond (nums)) :
    RPOrig.partitionEvensOdds nums h_precond = RPRef.partitionEvensOdds nums h_precond := by
  (simp [RPOrig.partitionEvensOdds, RPRef.partitionEvensOdds]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.partitionEvensOdds RPRef.partitionEvensOdds RPOrig.partitionEvensOdds.helper RPRef.partitionEvensOdds.helper; rfl))
