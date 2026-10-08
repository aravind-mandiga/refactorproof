-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def LinearSearch_precond (a : Array Int) (e : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def LinearSearch (a : Array Int) (e : Int) (h_precond : LinearSearch_precond (a) (e)) : Nat :=
  let rec loop (n : Nat) : Nat :=
    if n < a.size then
      if a[n]! = e then n
      else loop (n + 1)
    else n
  loop 0
end RPOrig

namespace RPRef

def LinearSearch (a : Array Int) (e : Int) (h_precond : LinearSearch_precond (a) (e)) : Nat :=
  let rec loop (n : Nat) : Nat :=
    if n < a.size then
      if a[n]! = e then n
      else loop (1 + n)
    else n
  loop 0
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (e : Int) (h_precond : LinearSearch_precond (a) (e)) :
    RPOrig.LinearSearch a e h_precond = RPRef.LinearSearch a e h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (e : Int) (h_precond : LinearSearch_precond (a) (e)) :
    RPOrig.LinearSearch a e h_precond = RPRef.LinearSearch a e h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (e : Int) (h_precond : LinearSearch_precond (a) (e)) :
    RPOrig.LinearSearch a e h_precond = RPRef.LinearSearch a e h_precond := by
  delta RPOrig.LinearSearch RPRef.LinearSearch RPOrig.LinearSearch.loop RPRef.LinearSearch.loop
  rfl

theorem rp_equiv_simp_only (a : Array Int) (e : Int) (h_precond : LinearSearch_precond (a) (e)) :
    RPOrig.LinearSearch a e h_precond = RPRef.LinearSearch a e h_precond := by
  first
    | (simp only [RPOrig.LinearSearch, RPRef.LinearSearch, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LinearSearch RPRef.LinearSearch RPOrig.LinearSearch.loop RPRef.LinearSearch.loop; rfl))
    | (simp only [RPOrig.LinearSearch, RPRef.LinearSearch, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LinearSearch RPRef.LinearSearch RPOrig.LinearSearch.loop RPRef.LinearSearch.loop; rfl))
    | (simp only [RPOrig.LinearSearch, RPRef.LinearSearch, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LinearSearch RPRef.LinearSearch RPOrig.LinearSearch.loop RPRef.LinearSearch.loop; rfl))
    | (simp only [RPOrig.LinearSearch, RPRef.LinearSearch]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LinearSearch RPRef.LinearSearch RPOrig.LinearSearch.loop RPRef.LinearSearch.loop; rfl))

theorem rp_equiv_simp (a : Array Int) (e : Int) (h_precond : LinearSearch_precond (a) (e)) :
    RPOrig.LinearSearch a e h_precond = RPRef.LinearSearch a e h_precond := by
  first
    | (simp [RPOrig.LinearSearch, RPRef.LinearSearch, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LinearSearch RPRef.LinearSearch RPOrig.LinearSearch.loop RPRef.LinearSearch.loop; rfl))
    | (simp [RPOrig.LinearSearch, RPRef.LinearSearch, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LinearSearch RPRef.LinearSearch RPOrig.LinearSearch.loop RPRef.LinearSearch.loop; rfl))
    | (simp [RPOrig.LinearSearch, RPRef.LinearSearch, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LinearSearch RPRef.LinearSearch RPOrig.LinearSearch.loop RPRef.LinearSearch.loop; rfl))
    | (simp [RPOrig.LinearSearch, RPRef.LinearSearch]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LinearSearch RPRef.LinearSearch RPOrig.LinearSearch.loop RPRef.LinearSearch.loop; rfl))

theorem rp_equiv_ac_rfl (a : Array Int) (e : Int) (h_precond : LinearSearch_precond (a) (e)) :
    RPOrig.LinearSearch a e h_precond = RPRef.LinearSearch a e h_precond := by
  (try simp only [RPOrig.LinearSearch, RPRef.LinearSearch]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LinearSearch RPRef.LinearSearch RPOrig.LinearSearch.loop RPRef.LinearSearch.loop; rfl))
