-- !benchmark @start import type=solution
import Std.Data.HashSet
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def findFirstRepeatedChar_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def findFirstRepeatedChar (s : String) (h_precond : findFirstRepeatedChar_precond (s)) : Option Char :=
  let cs := s.toList
  let rec loop (i : Nat) (seen : Std.HashSet Char) : Option Char :=
    if i < cs.length then
      let c := cs[i]!
      if seen.contains c then
        some c
      else
        loop (i + 1) (seen.insert c)
    else
      -- When no repeated char is found, return (false, arbitrary char)
      none
  loop 0 Std.HashSet.empty
end RPOrig

namespace RPRef

def findFirstRepeatedChar (s : String) (h_precond : findFirstRepeatedChar_precond (s)) : Option Char :=
  let cs := s.toList
  let rec loop (i : Nat) (seen : Std.HashSet Char) : Option Char :=
    if i < cs.length then
      let c := cs[i]!
      if seen.contains c then
        some c
      else
        loop (1 + i) (seen.insert c)
    else
      -- When no repeated char is found, return (false, arbitrary char)
      none
  loop 0 Std.HashSet.empty
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (s : String) (h_precond : findFirstRepeatedChar_precond (s)) :
    RPOrig.findFirstRepeatedChar s h_precond = RPRef.findFirstRepeatedChar s h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (s : String) (h_precond : findFirstRepeatedChar_precond (s)) :
    RPOrig.findFirstRepeatedChar s h_precond = RPRef.findFirstRepeatedChar s h_precond := rfl

theorem rp_equiv_delta_rfl (s : String) (h_precond : findFirstRepeatedChar_precond (s)) :
    RPOrig.findFirstRepeatedChar s h_precond = RPRef.findFirstRepeatedChar s h_precond := by
  delta RPOrig.findFirstRepeatedChar RPRef.findFirstRepeatedChar RPOrig.findFirstRepeatedChar.loop RPRef.findFirstRepeatedChar.loop
  rfl

theorem rp_equiv_simp_only (s : String) (h_precond : findFirstRepeatedChar_precond (s)) :
    RPOrig.findFirstRepeatedChar s h_precond = RPRef.findFirstRepeatedChar s h_precond := by
  first
    | (simp only [RPOrig.findFirstRepeatedChar, RPRef.findFirstRepeatedChar, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findFirstRepeatedChar RPRef.findFirstRepeatedChar RPOrig.findFirstRepeatedChar.loop RPRef.findFirstRepeatedChar.loop; rfl))
    | (simp only [RPOrig.findFirstRepeatedChar, RPRef.findFirstRepeatedChar, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findFirstRepeatedChar RPRef.findFirstRepeatedChar RPOrig.findFirstRepeatedChar.loop RPRef.findFirstRepeatedChar.loop; rfl))
    | (simp only [RPOrig.findFirstRepeatedChar, RPRef.findFirstRepeatedChar, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findFirstRepeatedChar RPRef.findFirstRepeatedChar RPOrig.findFirstRepeatedChar.loop RPRef.findFirstRepeatedChar.loop; rfl))
    | (simp only [RPOrig.findFirstRepeatedChar, RPRef.findFirstRepeatedChar]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findFirstRepeatedChar RPRef.findFirstRepeatedChar RPOrig.findFirstRepeatedChar.loop RPRef.findFirstRepeatedChar.loop; rfl))

theorem rp_equiv_simp (s : String) (h_precond : findFirstRepeatedChar_precond (s)) :
    RPOrig.findFirstRepeatedChar s h_precond = RPRef.findFirstRepeatedChar s h_precond := by
  first
    | (simp [RPOrig.findFirstRepeatedChar, RPRef.findFirstRepeatedChar, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findFirstRepeatedChar RPRef.findFirstRepeatedChar RPOrig.findFirstRepeatedChar.loop RPRef.findFirstRepeatedChar.loop; rfl))
    | (simp [RPOrig.findFirstRepeatedChar, RPRef.findFirstRepeatedChar, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findFirstRepeatedChar RPRef.findFirstRepeatedChar RPOrig.findFirstRepeatedChar.loop RPRef.findFirstRepeatedChar.loop; rfl))
    | (simp [RPOrig.findFirstRepeatedChar, RPRef.findFirstRepeatedChar, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findFirstRepeatedChar RPRef.findFirstRepeatedChar RPOrig.findFirstRepeatedChar.loop RPRef.findFirstRepeatedChar.loop; rfl))
    | (simp [RPOrig.findFirstRepeatedChar, RPRef.findFirstRepeatedChar]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findFirstRepeatedChar RPRef.findFirstRepeatedChar RPOrig.findFirstRepeatedChar.loop RPRef.findFirstRepeatedChar.loop; rfl))

theorem rp_equiv_ac_rfl (s : String) (h_precond : findFirstRepeatedChar_precond (s)) :
    RPOrig.findFirstRepeatedChar s h_precond = RPRef.findFirstRepeatedChar s h_precond := by
  (try simp only [RPOrig.findFirstRepeatedChar, RPRef.findFirstRepeatedChar]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findFirstRepeatedChar RPRef.findFirstRepeatedChar RPOrig.findFirstRepeatedChar.loop RPRef.findFirstRepeatedChar.loop; rfl))
