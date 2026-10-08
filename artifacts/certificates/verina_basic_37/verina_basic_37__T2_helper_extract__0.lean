-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def findFirstOccurrence_precond (arr : Array Int) (target : Int) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· ≤ ·) arr.toList
  -- !benchmark @end precond



namespace RPOrig

def findFirstOccurrence (arr : Array Int) (target : Int) (h_precond : findFirstOccurrence_precond (arr) (target)) : Int :=
  let rec loop (i : Nat) : Int :=
    if i < arr.size then
      let a := arr[i]!
      if a = target then i
      else if a > target then -1
      else loop (i + 1)
    else -1
  loop 0
end RPOrig

namespace RPRef
private def findFirstOccurrence__rp_helper_2f798f80 (arr : Array Int) (target : Int) (h_precond : findFirstOccurrence_precond (arr) (target)) : Int :=
  let rec loop (i : Nat) : Int :=
    if i < arr.size then
      let a := arr[i]!
      if a = target then i
      else if a > target then -1
      else loop (i + 1)
    else -1
  loop 0

def findFirstOccurrence (arr : Array Int) (target : Int) (h_precond : findFirstOccurrence_precond (arr) (target)) : Int :=
  findFirstOccurrence__rp_helper_2f798f80 arr target h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (arr : Array Int) (target : Int) (h_precond : findFirstOccurrence_precond (arr) (target)) :
    RPOrig.findFirstOccurrence arr target h_precond = RPRef.findFirstOccurrence arr target h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (arr : Array Int) (target : Int) (h_precond : findFirstOccurrence_precond (arr) (target)) :
    RPOrig.findFirstOccurrence arr target h_precond = RPRef.findFirstOccurrence arr target h_precond := rfl

theorem rp_equiv_delta_rfl (arr : Array Int) (target : Int) (h_precond : findFirstOccurrence_precond (arr) (target)) :
    RPOrig.findFirstOccurrence arr target h_precond = RPRef.findFirstOccurrence arr target h_precond := by
  delta RPOrig.findFirstOccurrence RPRef.findFirstOccurrence RPRef.findFirstOccurrence__rp_helper_2f798f80 RPOrig.findFirstOccurrence.loop RPRef.findFirstOccurrence__rp_helper_2f798f80.loop
  rfl

theorem rp_equiv_simp_only (arr : Array Int) (target : Int) (h_precond : findFirstOccurrence_precond (arr) (target)) :
    RPOrig.findFirstOccurrence arr target h_precond = RPRef.findFirstOccurrence arr target h_precond := by
  (simp only [RPOrig.findFirstOccurrence, RPRef.findFirstOccurrence, RPRef.findFirstOccurrence__rp_helper_2f798f80]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findFirstOccurrence RPRef.findFirstOccurrence RPRef.findFirstOccurrence__rp_helper_2f798f80 RPOrig.findFirstOccurrence.loop RPRef.findFirstOccurrence__rp_helper_2f798f80.loop; rfl))

theorem rp_equiv_simp (arr : Array Int) (target : Int) (h_precond : findFirstOccurrence_precond (arr) (target)) :
    RPOrig.findFirstOccurrence arr target h_precond = RPRef.findFirstOccurrence arr target h_precond := by
  (simp [RPOrig.findFirstOccurrence, RPRef.findFirstOccurrence, RPRef.findFirstOccurrence__rp_helper_2f798f80]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findFirstOccurrence RPRef.findFirstOccurrence RPRef.findFirstOccurrence__rp_helper_2f798f80 RPOrig.findFirstOccurrence.loop RPRef.findFirstOccurrence__rp_helper_2f798f80.loop; rfl))
