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

def findFirstOccurrence (arr : Array Int) (target : Int) (h_precond : findFirstOccurrence_precond (arr) (target)) : Int :=
  let rec loop (i : Nat) : Int :=
    if i < arr.size then
      let a := arr[i]!
      if a = target then i
      else if a > target then -1
      else loop (1 + i)
    else -1
  loop 0
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (arr : Array Int) (target : Int) (h_precond : findFirstOccurrence_precond (arr) (target)) :
    RPOrig.findFirstOccurrence arr target h_precond = RPRef.findFirstOccurrence arr target h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (arr : Array Int) (target : Int) (h_precond : findFirstOccurrence_precond (arr) (target)) :
    RPOrig.findFirstOccurrence arr target h_precond = RPRef.findFirstOccurrence arr target h_precond := rfl

theorem rp_equiv_delta_rfl (arr : Array Int) (target : Int) (h_precond : findFirstOccurrence_precond (arr) (target)) :
    RPOrig.findFirstOccurrence arr target h_precond = RPRef.findFirstOccurrence arr target h_precond := by
  delta RPOrig.findFirstOccurrence RPRef.findFirstOccurrence RPOrig.findFirstOccurrence.loop RPRef.findFirstOccurrence.loop
  rfl

theorem rp_equiv_simp_only (arr : Array Int) (target : Int) (h_precond : findFirstOccurrence_precond (arr) (target)) :
    RPOrig.findFirstOccurrence arr target h_precond = RPRef.findFirstOccurrence arr target h_precond := by
  first
    | (simp only [RPOrig.findFirstOccurrence, RPRef.findFirstOccurrence, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findFirstOccurrence RPRef.findFirstOccurrence RPOrig.findFirstOccurrence.loop RPRef.findFirstOccurrence.loop; rfl))
    | (simp only [RPOrig.findFirstOccurrence, RPRef.findFirstOccurrence, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findFirstOccurrence RPRef.findFirstOccurrence RPOrig.findFirstOccurrence.loop RPRef.findFirstOccurrence.loop; rfl))
    | (simp only [RPOrig.findFirstOccurrence, RPRef.findFirstOccurrence, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findFirstOccurrence RPRef.findFirstOccurrence RPOrig.findFirstOccurrence.loop RPRef.findFirstOccurrence.loop; rfl))
    | (simp only [RPOrig.findFirstOccurrence, RPRef.findFirstOccurrence]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findFirstOccurrence RPRef.findFirstOccurrence RPOrig.findFirstOccurrence.loop RPRef.findFirstOccurrence.loop; rfl))

theorem rp_equiv_simp (arr : Array Int) (target : Int) (h_precond : findFirstOccurrence_precond (arr) (target)) :
    RPOrig.findFirstOccurrence arr target h_precond = RPRef.findFirstOccurrence arr target h_precond := by
  first
    | (simp [RPOrig.findFirstOccurrence, RPRef.findFirstOccurrence, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findFirstOccurrence RPRef.findFirstOccurrence RPOrig.findFirstOccurrence.loop RPRef.findFirstOccurrence.loop; rfl))
    | (simp [RPOrig.findFirstOccurrence, RPRef.findFirstOccurrence, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findFirstOccurrence RPRef.findFirstOccurrence RPOrig.findFirstOccurrence.loop RPRef.findFirstOccurrence.loop; rfl))
    | (simp [RPOrig.findFirstOccurrence, RPRef.findFirstOccurrence, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findFirstOccurrence RPRef.findFirstOccurrence RPOrig.findFirstOccurrence.loop RPRef.findFirstOccurrence.loop; rfl))
    | (simp [RPOrig.findFirstOccurrence, RPRef.findFirstOccurrence]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findFirstOccurrence RPRef.findFirstOccurrence RPOrig.findFirstOccurrence.loop RPRef.findFirstOccurrence.loop; rfl))

theorem rp_equiv_ac_rfl (arr : Array Int) (target : Int) (h_precond : findFirstOccurrence_precond (arr) (target)) :
    RPOrig.findFirstOccurrence arr target h_precond = RPRef.findFirstOccurrence arr target h_precond := by
  (try simp only [RPOrig.findFirstOccurrence, RPRef.findFirstOccurrence]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findFirstOccurrence RPRef.findFirstOccurrence RPOrig.findFirstOccurrence.loop RPRef.findFirstOccurrence.loop; rfl))
