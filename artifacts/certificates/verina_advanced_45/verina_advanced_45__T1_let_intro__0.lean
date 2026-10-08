-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def maxSubarraySum_precond (xs : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def maxSubarraySum (xs : List Int) (h_precond : maxSubarraySum_precond (xs)) : Int :=
  let rec helper (lst : List Int) (curMax : Int) (globalMax : Int) : Int :=
    match lst with
    | [] => globalMax
    | x :: rest =>
      let newCurMax := max x (curMax + x)
      let newGlobal := max globalMax newCurMax
      helper rest newCurMax newGlobal
  match xs with
  | [] => 0
  | x :: rest => helper rest x x
end RPOrig

namespace RPRef

def maxSubarraySum (xs : List Int) (h_precond : maxSubarraySum_precond (xs)) : Int :=
  let __rp_tmp_d5b79b54 : Int :=
    let rec helper (lst : List Int) (curMax : Int) (globalMax : Int) : Int :=
      match lst with
      | [] => globalMax
      | x :: rest =>
        let newCurMax := max x (curMax + x)
        let newGlobal := max globalMax newCurMax
        helper rest newCurMax newGlobal
    match xs with
    | [] => 0
    | x :: rest => helper rest x x
  __rp_tmp_d5b79b54
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (xs : List Int) (h_precond : maxSubarraySum_precond (xs)) :
    RPOrig.maxSubarraySum xs h_precond = RPRef.maxSubarraySum xs h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (xs : List Int) (h_precond : maxSubarraySum_precond (xs)) :
    RPOrig.maxSubarraySum xs h_precond = RPRef.maxSubarraySum xs h_precond := rfl

theorem rp_equiv_delta_rfl (xs : List Int) (h_precond : maxSubarraySum_precond (xs)) :
    RPOrig.maxSubarraySum xs h_precond = RPRef.maxSubarraySum xs h_precond := by
  delta RPOrig.maxSubarraySum RPRef.maxSubarraySum RPOrig.maxSubarraySum.helper RPRef.maxSubarraySum.helper
  rfl

theorem rp_equiv_simp_only (xs : List Int) (h_precond : maxSubarraySum_precond (xs)) :
    RPOrig.maxSubarraySum xs h_precond = RPRef.maxSubarraySum xs h_precond := by
  (simp only [RPOrig.maxSubarraySum, RPRef.maxSubarraySum]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxSubarraySum RPRef.maxSubarraySum RPOrig.maxSubarraySum.helper RPRef.maxSubarraySum.helper; rfl))

theorem rp_equiv_simp (xs : List Int) (h_precond : maxSubarraySum_precond (xs)) :
    RPOrig.maxSubarraySum xs h_precond = RPRef.maxSubarraySum xs h_precond := by
  (simp [RPOrig.maxSubarraySum, RPRef.maxSubarraySum]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxSubarraySum RPRef.maxSubarraySum RPOrig.maxSubarraySum.helper RPRef.maxSubarraySum.helper; rfl))
