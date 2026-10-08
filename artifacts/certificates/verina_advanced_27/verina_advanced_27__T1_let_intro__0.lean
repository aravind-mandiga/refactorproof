-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def longestCommonSubsequence_precond (s1 : String) (s2 : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def toCharList (s : String) : List Char :=
  s.data

def fromCharList (cs : List Char) : String :=
  cs.foldl (fun acc c => acc.push c) ""

def lcsAux (xs : List Char) (ys : List Char) : List Char :=
  match xs, ys with
  | [], _ => []
  | _, [] => []
  | x :: xs', y :: ys' =>
    if x == y then
      x :: lcsAux xs' ys'
    else
      let left  := lcsAux xs' (y :: ys')
      let right := lcsAux (x :: xs') ys'
      if left.length >= right.length then left else right
termination_by xs.length + ys.length

namespace RPOrig

def longestCommonSubsequence (s1 : String) (s2 : String) (h_precond : longestCommonSubsequence_precond (s1) (s2)) : String :=
  let xs := toCharList s1
  let ys := toCharList s2
  let resultList := lcsAux xs ys
  fromCharList resultList
end RPOrig

namespace RPRef

def longestCommonSubsequence (s1 : String) (s2 : String) (h_precond : longestCommonSubsequence_precond (s1) (s2)) : String :=
  let __rp_tmp_b1c27a26 : String :=
    let xs := toCharList s1
    let ys := toCharList s2
    let resultList := lcsAux xs ys
    fromCharList resultList
  __rp_tmp_b1c27a26
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (s1 : String) (s2 : String) (h_precond : longestCommonSubsequence_precond (s1) (s2)) :
    RPOrig.longestCommonSubsequence s1 s2 h_precond = RPRef.longestCommonSubsequence s1 s2 h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (s1 : String) (s2 : String) (h_precond : longestCommonSubsequence_precond (s1) (s2)) :
    RPOrig.longestCommonSubsequence s1 s2 h_precond = RPRef.longestCommonSubsequence s1 s2 h_precond := rfl

theorem rp_equiv_delta_rfl (s1 : String) (s2 : String) (h_precond : longestCommonSubsequence_precond (s1) (s2)) :
    RPOrig.longestCommonSubsequence s1 s2 h_precond = RPRef.longestCommonSubsequence s1 s2 h_precond := by
  delta RPOrig.longestCommonSubsequence RPRef.longestCommonSubsequence
  rfl

theorem rp_equiv_simp_only (s1 : String) (s2 : String) (h_precond : longestCommonSubsequence_precond (s1) (s2)) :
    RPOrig.longestCommonSubsequence s1 s2 h_precond = RPRef.longestCommonSubsequence s1 s2 h_precond := by
  (simp only [RPOrig.longestCommonSubsequence, RPRef.longestCommonSubsequence]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestCommonSubsequence RPRef.longestCommonSubsequence; rfl))

theorem rp_equiv_simp (s1 : String) (s2 : String) (h_precond : longestCommonSubsequence_precond (s1) (s2)) :
    RPOrig.longestCommonSubsequence s1 s2 h_precond = RPRef.longestCommonSubsequence s1 s2 h_precond := by
  (simp [RPOrig.longestCommonSubsequence, RPRef.longestCommonSubsequence]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestCommonSubsequence RPRef.longestCommonSubsequence; rfl))
