-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def lastPosition_precond (arr : Array Int) (elem : Int) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· ≤ ·) arr.toList
  -- !benchmark @end precond



namespace RPOrig

def lastPosition (arr : Array Int) (elem : Int) (h_precond : lastPosition_precond (arr) (elem)) : Int :=
  let rec loop (i : Nat) (pos : Int) : Int :=
    if i < arr.size then
      let a := arr[i]!
      if a = elem then loop (i + 1) i
      else loop (i + 1) pos
    else pos
  loop 0 (-1)
end RPOrig

namespace RPRef

def lastPosition (arr : Array Int) (elem : Int) (h_precond : lastPosition_precond (arr) (elem)) : Int :=
  let rec loop (i : Nat) (pos : Int) : Int :=
    if i < arr.size then
      let a := arr[i]!
      if a = elem then loop (1 + i) i
      else loop (i + 1) pos
    else pos
  loop 0 (-1)
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (arr : Array Int) (elem : Int) (h_precond : lastPosition_precond (arr) (elem)) :
    RPOrig.lastPosition arr elem h_precond = RPRef.lastPosition arr elem h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (arr : Array Int) (elem : Int) (h_precond : lastPosition_precond (arr) (elem)) :
    RPOrig.lastPosition arr elem h_precond = RPRef.lastPosition arr elem h_precond := rfl

theorem rp_equiv_delta_rfl (arr : Array Int) (elem : Int) (h_precond : lastPosition_precond (arr) (elem)) :
    RPOrig.lastPosition arr elem h_precond = RPRef.lastPosition arr elem h_precond := by
  delta RPOrig.lastPosition RPRef.lastPosition RPOrig.lastPosition.loop RPRef.lastPosition.loop
  rfl

theorem rp_equiv_simp_only (arr : Array Int) (elem : Int) (h_precond : lastPosition_precond (arr) (elem)) :
    RPOrig.lastPosition arr elem h_precond = RPRef.lastPosition arr elem h_precond := by
  first
    | (simp only [RPOrig.lastPosition, RPRef.lastPosition, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.lastPosition RPRef.lastPosition RPOrig.lastPosition.loop RPRef.lastPosition.loop; rfl))
    | (simp only [RPOrig.lastPosition, RPRef.lastPosition, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.lastPosition RPRef.lastPosition RPOrig.lastPosition.loop RPRef.lastPosition.loop; rfl))
    | (simp only [RPOrig.lastPosition, RPRef.lastPosition, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.lastPosition RPRef.lastPosition RPOrig.lastPosition.loop RPRef.lastPosition.loop; rfl))
    | (simp only [RPOrig.lastPosition, RPRef.lastPosition]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.lastPosition RPRef.lastPosition RPOrig.lastPosition.loop RPRef.lastPosition.loop; rfl))

theorem rp_equiv_simp (arr : Array Int) (elem : Int) (h_precond : lastPosition_precond (arr) (elem)) :
    RPOrig.lastPosition arr elem h_precond = RPRef.lastPosition arr elem h_precond := by
  first
    | (simp [RPOrig.lastPosition, RPRef.lastPosition, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.lastPosition RPRef.lastPosition RPOrig.lastPosition.loop RPRef.lastPosition.loop; rfl))
    | (simp [RPOrig.lastPosition, RPRef.lastPosition, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.lastPosition RPRef.lastPosition RPOrig.lastPosition.loop RPRef.lastPosition.loop; rfl))
    | (simp [RPOrig.lastPosition, RPRef.lastPosition, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.lastPosition RPRef.lastPosition RPOrig.lastPosition.loop RPRef.lastPosition.loop; rfl))
    | (simp [RPOrig.lastPosition, RPRef.lastPosition]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.lastPosition RPRef.lastPosition RPOrig.lastPosition.loop RPRef.lastPosition.loop; rfl))

theorem rp_equiv_ac_rfl (arr : Array Int) (elem : Int) (h_precond : lastPosition_precond (arr) (elem)) :
    RPOrig.lastPosition arr elem h_precond = RPRef.lastPosition arr elem h_precond := by
  (try simp only [RPOrig.lastPosition, RPRef.lastPosition]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.lastPosition RPRef.lastPosition RPOrig.lastPosition.loop RPRef.lastPosition.loop; rfl))
