-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def Match_precond (s : String) (p : String) : Prop :=
  -- !benchmark @start precond
  s.toList.length = p.toList.length
  -- !benchmark @end precond



namespace RPOrig

def Match (s : String) (p : String) (h_precond : Match_precond (s) (p)) : Bool :=
  let sList := s.toList
  let pList := p.toList
  let rec loop (i : Nat) : Bool :=
    if i < sList.length then
      if (sList[i]! ≠ pList[i]!) ∧ (pList[i]! ≠ '?') then false
      else loop (i + 1)
    else true
  loop 0
end RPOrig

namespace RPRef

def Match (s : String) (p : String) (h_precond : Match_precond (s) (p)) : Bool :=
  let sList := s.toList
  let pList := p.toList
  let rec loop (i : Nat) : Bool :=
    if i < sList.length then
      if (sList[i]! ≠ pList[i]!) ∧ (pList[i]! ≠ '?') then false
      else loop (1 + i)
    else true
  loop 0
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (s : String) (p : String) (h_precond : Match_precond (s) (p)) :
    RPOrig.Match s p h_precond = RPRef.Match s p h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (s : String) (p : String) (h_precond : Match_precond (s) (p)) :
    RPOrig.Match s p h_precond = RPRef.Match s p h_precond := rfl

theorem rp_equiv_delta_rfl (s : String) (p : String) (h_precond : Match_precond (s) (p)) :
    RPOrig.Match s p h_precond = RPRef.Match s p h_precond := by
  delta RPOrig.Match RPRef.Match RPOrig.Match.loop RPRef.Match.loop
  rfl

theorem rp_equiv_simp_only (s : String) (p : String) (h_precond : Match_precond (s) (p)) :
    RPOrig.Match s p h_precond = RPRef.Match s p h_precond := by
  first
    | (simp only [RPOrig.Match, RPRef.Match, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Match RPRef.Match RPOrig.Match.loop RPRef.Match.loop; rfl))
    | (simp only [RPOrig.Match, RPRef.Match, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Match RPRef.Match RPOrig.Match.loop RPRef.Match.loop; rfl))
    | (simp only [RPOrig.Match, RPRef.Match, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Match RPRef.Match RPOrig.Match.loop RPRef.Match.loop; rfl))
    | (simp only [RPOrig.Match, RPRef.Match]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Match RPRef.Match RPOrig.Match.loop RPRef.Match.loop; rfl))

theorem rp_equiv_simp (s : String) (p : String) (h_precond : Match_precond (s) (p)) :
    RPOrig.Match s p h_precond = RPRef.Match s p h_precond := by
  first
    | (simp [RPOrig.Match, RPRef.Match, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Match RPRef.Match RPOrig.Match.loop RPRef.Match.loop; rfl))
    | (simp [RPOrig.Match, RPRef.Match, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Match RPRef.Match RPOrig.Match.loop RPRef.Match.loop; rfl))
    | (simp [RPOrig.Match, RPRef.Match, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Match RPRef.Match RPOrig.Match.loop RPRef.Match.loop; rfl))
    | (simp [RPOrig.Match, RPRef.Match]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Match RPRef.Match RPOrig.Match.loop RPRef.Match.loop; rfl))

theorem rp_equiv_ac_rfl (s : String) (p : String) (h_precond : Match_precond (s) (p)) :
    RPOrig.Match s p h_precond = RPRef.Match s p h_precond := by
  (try simp only [RPOrig.Match, RPRef.Match]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Match RPRef.Match RPOrig.Match.loop RPRef.Match.loop; rfl))
