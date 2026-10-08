-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def LongestCommonSubsequence_precond (a : Array Int) (b : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def intMax (x y : Int) : Int :=
  if x < y then y else x

namespace RPOrig

def LongestCommonSubsequence (a : Array Int) (b : Array Int) (h_precond : LongestCommonSubsequence_precond (a) (b)) : Int :=
  let m := a.size
  let n := b.size

  let dp := Id.run do
    let mut dp := Array.mkArray (m + 1) (Array.mkArray (n + 1) 0)
    for i in List.range (m + 1) do
      for j in List.range (n + 1) do
        if i = 0 ∨ j = 0 then
          ()
        else if a[i - 1]! = b[j - 1]! then
          let newVal := ((dp[i - 1]!)[j - 1]!) + 1
          dp := dp.set! i (dp[i]!.set! j newVal)
        else
          let newVal := intMax ((dp[i - 1]!)[j]!) ((dp[i]!)[j - 1]!)
          dp := dp.set! i (dp[i]!.set! j newVal)
    return dp
  (dp[m]!)[n]!
end RPOrig

namespace RPRef

def LongestCommonSubsequence (a : Array Int) (b : Array Int) (h_precond : LongestCommonSubsequence_precond (a) (b)) : Int :=
  let m := a.size
  let n := b.size

  let dp := Id.run do
    let mut dp := Array.mkArray (m + 1) (Array.mkArray (n + 1) 0)
    for i in List.range (1 + m) do
      for j in List.range (n + 1) do
        if i = 0 ∨ j = 0 then
          ()
        else if a[i - 1]! = b[j - 1]! then
          let newVal := ((dp[i - 1]!)[j - 1]!) + 1
          dp := dp.set! i (dp[i]!.set! j newVal)
        else
          let newVal := intMax ((dp[i - 1]!)[j]!) ((dp[i]!)[j - 1]!)
          dp := dp.set! i (dp[i]!.set! j newVal)
    return dp
  (dp[m]!)[n]!
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (b : Array Int) (h_precond : LongestCommonSubsequence_precond (a) (b)) :
    RPOrig.LongestCommonSubsequence a b h_precond = RPRef.LongestCommonSubsequence a b h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (b : Array Int) (h_precond : LongestCommonSubsequence_precond (a) (b)) :
    RPOrig.LongestCommonSubsequence a b h_precond = RPRef.LongestCommonSubsequence a b h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (b : Array Int) (h_precond : LongestCommonSubsequence_precond (a) (b)) :
    RPOrig.LongestCommonSubsequence a b h_precond = RPRef.LongestCommonSubsequence a b h_precond := by
  delta RPOrig.LongestCommonSubsequence RPRef.LongestCommonSubsequence
  rfl

theorem rp_equiv_simp_only (a : Array Int) (b : Array Int) (h_precond : LongestCommonSubsequence_precond (a) (b)) :
    RPOrig.LongestCommonSubsequence a b h_precond = RPRef.LongestCommonSubsequence a b h_precond := by
  first
    | (simp only [RPOrig.LongestCommonSubsequence, RPRef.LongestCommonSubsequence, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LongestCommonSubsequence RPRef.LongestCommonSubsequence; rfl))
    | (simp only [RPOrig.LongestCommonSubsequence, RPRef.LongestCommonSubsequence, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LongestCommonSubsequence RPRef.LongestCommonSubsequence; rfl))
    | (simp only [RPOrig.LongestCommonSubsequence, RPRef.LongestCommonSubsequence, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LongestCommonSubsequence RPRef.LongestCommonSubsequence; rfl))
    | (simp only [RPOrig.LongestCommonSubsequence, RPRef.LongestCommonSubsequence]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LongestCommonSubsequence RPRef.LongestCommonSubsequence; rfl))

theorem rp_equiv_simp (a : Array Int) (b : Array Int) (h_precond : LongestCommonSubsequence_precond (a) (b)) :
    RPOrig.LongestCommonSubsequence a b h_precond = RPRef.LongestCommonSubsequence a b h_precond := by
  first
    | (simp [RPOrig.LongestCommonSubsequence, RPRef.LongestCommonSubsequence, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LongestCommonSubsequence RPRef.LongestCommonSubsequence; rfl))
    | (simp [RPOrig.LongestCommonSubsequence, RPRef.LongestCommonSubsequence, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LongestCommonSubsequence RPRef.LongestCommonSubsequence; rfl))
    | (simp [RPOrig.LongestCommonSubsequence, RPRef.LongestCommonSubsequence, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LongestCommonSubsequence RPRef.LongestCommonSubsequence; rfl))
    | (simp [RPOrig.LongestCommonSubsequence, RPRef.LongestCommonSubsequence]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LongestCommonSubsequence RPRef.LongestCommonSubsequence; rfl))

theorem rp_equiv_ac_rfl (a : Array Int) (b : Array Int) (h_precond : LongestCommonSubsequence_precond (a) (b)) :
    RPOrig.LongestCommonSubsequence a b h_precond = RPRef.LongestCommonSubsequence a b h_precond := by
  (try simp only [RPOrig.LongestCommonSubsequence, RPRef.LongestCommonSubsequence]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LongestCommonSubsequence RPRef.LongestCommonSubsequence; rfl))
