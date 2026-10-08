-- !benchmark @start import type=solution
import Std.Data.HashMap
-- !benchmark @end import

-- !benchmark @start solution_aux
open Std
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def mostFrequent_precond (xs : List Int) : Prop :=
  -- !benchmark @start precond
  xs ≠ []
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
-- Build a frequency map from the list
def countMap (xs : List Int) : HashMap Int Nat :=
  let step := fun m x =>
    let current := m.getD x 0
    m.insert x (current + 1)
  let init := (HashMap.emptyWithCapacity : HashMap Int Nat)
  xs.foldl step init

-- Compute the maximum frequency in the map
def getMaxFrequency (m : HashMap Int Nat) : Nat :=
  let step := fun acc (_k, v) =>
    if v > acc then v else acc
  let init := 0
  m.toList.foldl step init

-- Extract all keys whose frequency == maxFreq
def getCandidates (m : HashMap Int Nat) (maxFreq : Nat) : List Int :=
  let isTarget := fun (_k, v) => v = maxFreq
  let extract := fun (k, _) => k
  m.toList.filter isTarget |>.map extract

-- Return the first candidate element from original list
def getFirstWithFreq (xs : List Int) (candidates : List Int) : Int :=
  match xs.find? (fun x => candidates.contains x) with
  | some x => x
  | none => 0

namespace RPOrig

def mostFrequent (xs : List Int) (h_precond : mostFrequent_precond (xs)) : Int :=
  let freqMap := countMap xs
  let maxF := getMaxFrequency freqMap
  let candidates := getCandidates freqMap maxF
  getFirstWithFreq xs candidates
end RPOrig

namespace RPRef

private def mostFrequent__rp_helper_6e447617 (xs : List Int) (h_precond : mostFrequent_precond (xs)) : Int :=
  let freqMap := countMap xs
  let maxF := getMaxFrequency freqMap
  let candidates := getCandidates freqMap maxF
  getFirstWithFreq xs candidates

def mostFrequent (xs : List Int) (h_precond : mostFrequent_precond (xs)) : Int :=
  mostFrequent__rp_helper_6e447617 xs h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (xs : List Int) (h_precond : mostFrequent_precond (xs)) :
    RPOrig.mostFrequent xs h_precond = RPRef.mostFrequent xs h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (xs : List Int) (h_precond : mostFrequent_precond (xs)) :
    RPOrig.mostFrequent xs h_precond = RPRef.mostFrequent xs h_precond := rfl

theorem rp_equiv_delta_rfl (xs : List Int) (h_precond : mostFrequent_precond (xs)) :
    RPOrig.mostFrequent xs h_precond = RPRef.mostFrequent xs h_precond := by
  delta RPOrig.mostFrequent RPRef.mostFrequent RPRef.mostFrequent__rp_helper_6e447617
  rfl

theorem rp_equiv_simp_only (xs : List Int) (h_precond : mostFrequent_precond (xs)) :
    RPOrig.mostFrequent xs h_precond = RPRef.mostFrequent xs h_precond := by
  (simp only [RPOrig.mostFrequent, RPRef.mostFrequent, RPRef.mostFrequent__rp_helper_6e447617]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.mostFrequent RPRef.mostFrequent RPRef.mostFrequent__rp_helper_6e447617; rfl))

theorem rp_equiv_simp (xs : List Int) (h_precond : mostFrequent_precond (xs)) :
    RPOrig.mostFrequent xs h_precond = RPRef.mostFrequent xs h_precond := by
  (simp [RPOrig.mostFrequent, RPRef.mostFrequent, RPRef.mostFrequent__rp_helper_6e447617]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.mostFrequent RPRef.mostFrequent RPRef.mostFrequent__rp_helper_6e447617; rfl))
