-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isSorted_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def isSorted (a : Array Int) (h_precond : isSorted_precond (a)) : Bool :=
  if a.size ≤ 1 then
    true
  else
    a.mapIdx (fun i x =>
      if h : i + 1 < a.size then
        decide (x ≤ a[i + 1])
      else
        true) |>.all id
end RPOrig

namespace RPRef

def isSorted (a : Array Int) (h_precond : isSorted_precond (a)) : Bool :=
  if a.size ≤ 1 then
    true
  else
    a.mapIdx (fun i x =>
      if h : i + 1 < a.size then
        decide (x ≤ a[1 + i])
      else
        true) |>.all id
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (h_precond : isSorted_precond (a)) :
    RPOrig.isSorted a h_precond = RPRef.isSorted a h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (h_precond : isSorted_precond (a)) :
    RPOrig.isSorted a h_precond = RPRef.isSorted a h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (h_precond : isSorted_precond (a)) :
    RPOrig.isSorted a h_precond = RPRef.isSorted a h_precond := by
  delta RPOrig.isSorted RPRef.isSorted
  rfl

theorem rp_equiv_simp_only (a : Array Int) (h_precond : isSorted_precond (a)) :
    RPOrig.isSorted a h_precond = RPRef.isSorted a h_precond := by
  first
    | (simp only [RPOrig.isSorted, RPRef.isSorted, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isSorted RPRef.isSorted; rfl))
    | (simp only [RPOrig.isSorted, RPRef.isSorted, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isSorted RPRef.isSorted; rfl))
    | (simp only [RPOrig.isSorted, RPRef.isSorted, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isSorted RPRef.isSorted; rfl))
    | (simp only [RPOrig.isSorted, RPRef.isSorted]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isSorted RPRef.isSorted; rfl))

theorem rp_equiv_simp (a : Array Int) (h_precond : isSorted_precond (a)) :
    RPOrig.isSorted a h_precond = RPRef.isSorted a h_precond := by
  first
    | (simp [RPOrig.isSorted, RPRef.isSorted, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isSorted RPRef.isSorted; rfl))
    | (simp [RPOrig.isSorted, RPRef.isSorted, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isSorted RPRef.isSorted; rfl))
    | (simp [RPOrig.isSorted, RPRef.isSorted, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isSorted RPRef.isSorted; rfl))
    | (simp [RPOrig.isSorted, RPRef.isSorted]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isSorted RPRef.isSorted; rfl))

theorem rp_equiv_ac_rfl (a : Array Int) (h_precond : isSorted_precond (a)) :
    RPOrig.isSorted a h_precond = RPRef.isSorted a h_precond := by
  (try simp only [RPOrig.isSorted, RPRef.isSorted]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isSorted RPRef.isSorted; rfl))
