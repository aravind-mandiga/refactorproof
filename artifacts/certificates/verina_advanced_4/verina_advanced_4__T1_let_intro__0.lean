-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def LongestIncreasingSubsequence_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def intMax (x y : Int) : Int :=
  if x < y then y else x

namespace RPOrig

def LongestIncreasingSubsequence (a : Array Int) (h_precond : LongestIncreasingSubsequence_precond (a)) : Int :=
  let n := a.size
  let dp := Id.run do
    let mut dp := Array.mkArray n 1
    for i in [1:n] do
      for j in [0:i] do
        if a[j]! < a[i]! then
          let newVal := intMax (dp[i]!) (dp[j]! + 1)
          dp := dp.set! i newVal
    return dp
  match dp with
  | #[] => 0
  | _   => dp.foldl intMax 0
end RPOrig

namespace RPRef

def LongestIncreasingSubsequence (a : Array Int) (h_precond : LongestIncreasingSubsequence_precond (a)) : Int :=
  let __rp_tmp_e5a1307e : Int :=
    let n := a.size
    let dp := Id.run do
      let mut dp := Array.mkArray n 1
      for i in [1:n] do
        for j in [0:i] do
          if a[j]! < a[i]! then
            let newVal := intMax (dp[i]!) (dp[j]! + 1)
            dp := dp.set! i newVal
      return dp
    match dp with
    | #[] => 0
    | _   => dp.foldl intMax 0
  __rp_tmp_e5a1307e
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (h_precond : LongestIncreasingSubsequence_precond (a)) :
    RPOrig.LongestIncreasingSubsequence a h_precond = RPRef.LongestIncreasingSubsequence a h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (h_precond : LongestIncreasingSubsequence_precond (a)) :
    RPOrig.LongestIncreasingSubsequence a h_precond = RPRef.LongestIncreasingSubsequence a h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (h_precond : LongestIncreasingSubsequence_precond (a)) :
    RPOrig.LongestIncreasingSubsequence a h_precond = RPRef.LongestIncreasingSubsequence a h_precond := by
  delta RPOrig.LongestIncreasingSubsequence RPRef.LongestIncreasingSubsequence
  rfl

theorem rp_equiv_simp_only (a : Array Int) (h_precond : LongestIncreasingSubsequence_precond (a)) :
    RPOrig.LongestIncreasingSubsequence a h_precond = RPRef.LongestIncreasingSubsequence a h_precond := by
  (simp only [RPOrig.LongestIncreasingSubsequence, RPRef.LongestIncreasingSubsequence]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LongestIncreasingSubsequence RPRef.LongestIncreasingSubsequence; rfl))

theorem rp_equiv_simp (a : Array Int) (h_precond : LongestIncreasingSubsequence_precond (a)) :
    RPOrig.LongestIncreasingSubsequence a h_precond = RPRef.LongestIncreasingSubsequence a h_precond := by
  (simp [RPOrig.LongestIncreasingSubsequence, RPRef.LongestIncreasingSubsequence]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LongestIncreasingSubsequence RPRef.LongestIncreasingSubsequence; rfl))
