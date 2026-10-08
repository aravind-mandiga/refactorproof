-- !benchmark @start import type=solution
import Mathlib.Data.List.Basic
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def longestIncreasingSubseqLength_precond (xs : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
-- Generate all subsequences
def subsequences {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs =>
    let subs := subsequences xs
    subs ++ subs.map (fun s => x :: s)

-- Check if a list is strictly increasing
def isStrictlyIncreasing : List Int → Bool
  | [] => true
  | [_] => true
  | x :: y :: rest => if x < y then isStrictlyIncreasing (y :: rest) else false

namespace RPOrig

def longestIncreasingSubseqLength (xs : List Int) (h_precond : longestIncreasingSubseqLength_precond (xs)) : Nat :=
  let subs := subsequences xs
  let increasing := subs.filter isStrictlyIncreasing
  increasing.foldl (fun acc s => max acc s.length) 0
end RPOrig

namespace RPRef

private def longestIncreasingSubseqLength__rp_helper_bdb11251 (xs : List Int) (h_precond : longestIncreasingSubseqLength_precond (xs)) : Nat :=
  let subs := subsequences xs
  let increasing := subs.filter isStrictlyIncreasing
  increasing.foldl (fun acc s => max acc s.length) 0

def longestIncreasingSubseqLength (xs : List Int) (h_precond : longestIncreasingSubseqLength_precond (xs)) : Nat :=
  longestIncreasingSubseqLength__rp_helper_bdb11251 xs h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (xs : List Int) (h_precond : longestIncreasingSubseqLength_precond (xs)) :
    RPOrig.longestIncreasingSubseqLength xs h_precond = RPRef.longestIncreasingSubseqLength xs h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (xs : List Int) (h_precond : longestIncreasingSubseqLength_precond (xs)) :
    RPOrig.longestIncreasingSubseqLength xs h_precond = RPRef.longestIncreasingSubseqLength xs h_precond := rfl

theorem rp_equiv_delta_rfl (xs : List Int) (h_precond : longestIncreasingSubseqLength_precond (xs)) :
    RPOrig.longestIncreasingSubseqLength xs h_precond = RPRef.longestIncreasingSubseqLength xs h_precond := by
  delta RPOrig.longestIncreasingSubseqLength RPRef.longestIncreasingSubseqLength RPRef.longestIncreasingSubseqLength__rp_helper_bdb11251
  rfl

theorem rp_equiv_simp_only (xs : List Int) (h_precond : longestIncreasingSubseqLength_precond (xs)) :
    RPOrig.longestIncreasingSubseqLength xs h_precond = RPRef.longestIncreasingSubseqLength xs h_precond := by
  (simp only [RPOrig.longestIncreasingSubseqLength, RPRef.longestIncreasingSubseqLength, RPRef.longestIncreasingSubseqLength__rp_helper_bdb11251]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestIncreasingSubseqLength RPRef.longestIncreasingSubseqLength RPRef.longestIncreasingSubseqLength__rp_helper_bdb11251; rfl))

theorem rp_equiv_simp (xs : List Int) (h_precond : longestIncreasingSubseqLength_precond (xs)) :
    RPOrig.longestIncreasingSubseqLength xs h_precond = RPRef.longestIncreasingSubseqLength xs h_precond := by
  (simp [RPOrig.longestIncreasingSubseqLength, RPRef.longestIncreasingSubseqLength, RPRef.longestIncreasingSubseqLength__rp_helper_bdb11251]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestIncreasingSubseqLength RPRef.longestIncreasingSubseqLength RPRef.longestIncreasingSubseqLength__rp_helper_bdb11251; rfl))
