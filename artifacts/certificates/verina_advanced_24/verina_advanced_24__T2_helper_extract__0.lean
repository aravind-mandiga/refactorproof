-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def lengthOfLIS_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def lengthOfLIS (nums : List Int) (h_precond : lengthOfLIS_precond (nums)) : Int :=
  let rec lisHelper (dp : List Int) (x : Int) : List Int :=
    let rec replace (l : List Int) (acc : List Int) : List Int :=
      match l with
      | [] => (acc.reverse ++ [x])
      | y :: ys => if x ≤ y then acc.reverse ++ (x :: ys) else replace ys (y :: acc)
    replace dp []

  let finalDP := nums.foldl lisHelper []
  finalDP.length
end RPOrig

namespace RPRef
private def lengthOfLIS__rp_helper_1b403893 (nums : List Int) (h_precond : lengthOfLIS_precond (nums)) : Int :=
  let rec lisHelper (dp : List Int) (x : Int) : List Int :=
    let rec replace (l : List Int) (acc : List Int) : List Int :=
      match l with
      | [] => (acc.reverse ++ [x])
      | y :: ys => if x ≤ y then acc.reverse ++ (x :: ys) else replace ys (y :: acc)
    replace dp []

  let finalDP := nums.foldl lisHelper []
  finalDP.length

def lengthOfLIS (nums : List Int) (h_precond : lengthOfLIS_precond (nums)) : Int :=
  lengthOfLIS__rp_helper_1b403893 nums h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (nums : List Int) (h_precond : lengthOfLIS_precond (nums)) :
    RPOrig.lengthOfLIS nums h_precond = RPRef.lengthOfLIS nums h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (nums : List Int) (h_precond : lengthOfLIS_precond (nums)) :
    RPOrig.lengthOfLIS nums h_precond = RPRef.lengthOfLIS nums h_precond := rfl

theorem rp_equiv_delta_rfl (nums : List Int) (h_precond : lengthOfLIS_precond (nums)) :
    RPOrig.lengthOfLIS nums h_precond = RPRef.lengthOfLIS nums h_precond := by
  delta RPOrig.lengthOfLIS RPRef.lengthOfLIS RPRef.lengthOfLIS__rp_helper_1b403893 RPOrig.lengthOfLIS.lisHelper RPOrig.lengthOfLIS.replace RPRef.lengthOfLIS__rp_helper_1b403893.lisHelper RPRef.lengthOfLIS__rp_helper_1b403893.replace
  rfl

theorem rp_equiv_simp_only (nums : List Int) (h_precond : lengthOfLIS_precond (nums)) :
    RPOrig.lengthOfLIS nums h_precond = RPRef.lengthOfLIS nums h_precond := by
  (simp only [RPOrig.lengthOfLIS, RPRef.lengthOfLIS, RPRef.lengthOfLIS__rp_helper_1b403893]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.lengthOfLIS RPRef.lengthOfLIS RPRef.lengthOfLIS__rp_helper_1b403893 RPOrig.lengthOfLIS.lisHelper RPOrig.lengthOfLIS.replace RPRef.lengthOfLIS__rp_helper_1b403893.lisHelper RPRef.lengthOfLIS__rp_helper_1b403893.replace; rfl))

theorem rp_equiv_simp (nums : List Int) (h_precond : lengthOfLIS_precond (nums)) :
    RPOrig.lengthOfLIS nums h_precond = RPRef.lengthOfLIS nums h_precond := by
  (simp [RPOrig.lengthOfLIS, RPRef.lengthOfLIS, RPRef.lengthOfLIS__rp_helper_1b403893]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.lengthOfLIS RPRef.lengthOfLIS RPRef.lengthOfLIS__rp_helper_1b403893 RPOrig.lengthOfLIS.lisHelper RPOrig.lengthOfLIS.replace RPRef.lengthOfLIS__rp_helper_1b403893.lisHelper RPRef.lengthOfLIS__rp_helper_1b403893.replace; rfl))
