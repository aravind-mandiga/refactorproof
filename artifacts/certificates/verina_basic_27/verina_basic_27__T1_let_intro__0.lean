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
  let __rp_tmp_188cb1b2 : Option Char :=
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
  __rp_tmp_188cb1b2
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
  (simp only [RPOrig.findFirstRepeatedChar, RPRef.findFirstRepeatedChar]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findFirstRepeatedChar RPRef.findFirstRepeatedChar RPOrig.findFirstRepeatedChar.loop RPRef.findFirstRepeatedChar.loop; rfl))

theorem rp_equiv_simp (s : String) (h_precond : findFirstRepeatedChar_precond (s)) :
    RPOrig.findFirstRepeatedChar s h_precond = RPRef.findFirstRepeatedChar s h_precond := by
  (simp [RPOrig.findFirstRepeatedChar, RPRef.findFirstRepeatedChar]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findFirstRepeatedChar RPRef.findFirstRepeatedChar RPOrig.findFirstRepeatedChar.loop RPRef.findFirstRepeatedChar.loop; rfl))
