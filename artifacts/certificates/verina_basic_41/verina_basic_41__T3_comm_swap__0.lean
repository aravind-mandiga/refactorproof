-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def hasOnlyOneDistinctElement_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0
  -- !benchmark @end precond



namespace RPOrig

def hasOnlyOneDistinctElement (a : Array Int) (h_precond : hasOnlyOneDistinctElement_precond (a)) : Bool :=
  if a.size = 0 then
    true
  else
    let firstElement := a[0]!
    let rec loop (i : Nat) : Bool :=
      if h : i < a.size then
        if a[i]! = firstElement then loop (i + 1) else false
      else
        true
    loop 1
end RPOrig

namespace RPRef

def hasOnlyOneDistinctElement (a : Array Int) (h_precond : hasOnlyOneDistinctElement_precond (a)) : Bool :=
  if a.size = 0 then
    true
  else
    let firstElement := a[0]!
    let rec loop (i : Nat) : Bool :=
      if h : i < a.size then
        if a[i]! = firstElement then loop (1 + i) else false
      else
        true
    loop 1
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (h_precond : hasOnlyOneDistinctElement_precond (a)) :
    RPOrig.hasOnlyOneDistinctElement a h_precond = RPRef.hasOnlyOneDistinctElement a h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (h_precond : hasOnlyOneDistinctElement_precond (a)) :
    RPOrig.hasOnlyOneDistinctElement a h_precond = RPRef.hasOnlyOneDistinctElement a h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (h_precond : hasOnlyOneDistinctElement_precond (a)) :
    RPOrig.hasOnlyOneDistinctElement a h_precond = RPRef.hasOnlyOneDistinctElement a h_precond := by
  delta RPOrig.hasOnlyOneDistinctElement RPRef.hasOnlyOneDistinctElement RPOrig.hasOnlyOneDistinctElement.loop RPRef.hasOnlyOneDistinctElement.loop
  rfl

theorem rp_equiv_simp_only (a : Array Int) (h_precond : hasOnlyOneDistinctElement_precond (a)) :
    RPOrig.hasOnlyOneDistinctElement a h_precond = RPRef.hasOnlyOneDistinctElement a h_precond := by
  first
    | (simp only [RPOrig.hasOnlyOneDistinctElement, RPRef.hasOnlyOneDistinctElement, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.hasOnlyOneDistinctElement RPRef.hasOnlyOneDistinctElement RPOrig.hasOnlyOneDistinctElement.loop RPRef.hasOnlyOneDistinctElement.loop; rfl))
    | (simp only [RPOrig.hasOnlyOneDistinctElement, RPRef.hasOnlyOneDistinctElement, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.hasOnlyOneDistinctElement RPRef.hasOnlyOneDistinctElement RPOrig.hasOnlyOneDistinctElement.loop RPRef.hasOnlyOneDistinctElement.loop; rfl))
    | (simp only [RPOrig.hasOnlyOneDistinctElement, RPRef.hasOnlyOneDistinctElement, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.hasOnlyOneDistinctElement RPRef.hasOnlyOneDistinctElement RPOrig.hasOnlyOneDistinctElement.loop RPRef.hasOnlyOneDistinctElement.loop; rfl))
    | (simp only [RPOrig.hasOnlyOneDistinctElement, RPRef.hasOnlyOneDistinctElement]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.hasOnlyOneDistinctElement RPRef.hasOnlyOneDistinctElement RPOrig.hasOnlyOneDistinctElement.loop RPRef.hasOnlyOneDistinctElement.loop; rfl))

theorem rp_equiv_simp (a : Array Int) (h_precond : hasOnlyOneDistinctElement_precond (a)) :
    RPOrig.hasOnlyOneDistinctElement a h_precond = RPRef.hasOnlyOneDistinctElement a h_precond := by
  first
    | (simp [RPOrig.hasOnlyOneDistinctElement, RPRef.hasOnlyOneDistinctElement, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.hasOnlyOneDistinctElement RPRef.hasOnlyOneDistinctElement RPOrig.hasOnlyOneDistinctElement.loop RPRef.hasOnlyOneDistinctElement.loop; rfl))
    | (simp [RPOrig.hasOnlyOneDistinctElement, RPRef.hasOnlyOneDistinctElement, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.hasOnlyOneDistinctElement RPRef.hasOnlyOneDistinctElement RPOrig.hasOnlyOneDistinctElement.loop RPRef.hasOnlyOneDistinctElement.loop; rfl))
    | (simp [RPOrig.hasOnlyOneDistinctElement, RPRef.hasOnlyOneDistinctElement, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.hasOnlyOneDistinctElement RPRef.hasOnlyOneDistinctElement RPOrig.hasOnlyOneDistinctElement.loop RPRef.hasOnlyOneDistinctElement.loop; rfl))
    | (simp [RPOrig.hasOnlyOneDistinctElement, RPRef.hasOnlyOneDistinctElement]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.hasOnlyOneDistinctElement RPRef.hasOnlyOneDistinctElement RPOrig.hasOnlyOneDistinctElement.loop RPRef.hasOnlyOneDistinctElement.loop; rfl))

theorem rp_equiv_ac_rfl (a : Array Int) (h_precond : hasOnlyOneDistinctElement_precond (a)) :
    RPOrig.hasOnlyOneDistinctElement a h_precond = RPRef.hasOnlyOneDistinctElement a h_precond := by
  (try simp only [RPOrig.hasOnlyOneDistinctElement, RPRef.hasOnlyOneDistinctElement]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.hasOnlyOneDistinctElement RPRef.hasOnlyOneDistinctElement RPOrig.hasOnlyOneDistinctElement.loop RPRef.hasOnlyOneDistinctElement.loop; rfl))
