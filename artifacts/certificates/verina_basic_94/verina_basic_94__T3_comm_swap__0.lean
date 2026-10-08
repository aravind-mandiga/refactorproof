-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def iter_copy_precond (s : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def iter_copy (s : Array Int) (h_precond : iter_copy_precond (s)) : Array Int :=
  let rec loop (i : Nat) (acc : Array Int) : Array Int :=
    if i < s.size then
      match s[i]? with
      | some val => loop (i + 1) (acc.push val)
      | none => acc  -- This case shouldn't happen when i < s.size
    else
      acc
  loop 0 Array.empty
end RPOrig

namespace RPRef

def iter_copy (s : Array Int) (h_precond : iter_copy_precond (s)) : Array Int :=
  let rec loop (i : Nat) (acc : Array Int) : Array Int :=
    if i < s.size then
      match s[i]? with
      | some val => loop (1 + i) (acc.push val)
      | none => acc  -- This case shouldn't happen when i < s.size
    else
      acc
  loop 0 Array.empty
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (s : Array Int) (h_precond : iter_copy_precond (s)) :
    RPOrig.iter_copy s h_precond = RPRef.iter_copy s h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (s : Array Int) (h_precond : iter_copy_precond (s)) :
    RPOrig.iter_copy s h_precond = RPRef.iter_copy s h_precond := rfl

theorem rp_equiv_delta_rfl (s : Array Int) (h_precond : iter_copy_precond (s)) :
    RPOrig.iter_copy s h_precond = RPRef.iter_copy s h_precond := by
  delta RPOrig.iter_copy RPRef.iter_copy RPOrig.iter_copy.loop RPRef.iter_copy.loop
  rfl

theorem rp_equiv_simp_only (s : Array Int) (h_precond : iter_copy_precond (s)) :
    RPOrig.iter_copy s h_precond = RPRef.iter_copy s h_precond := by
  first
    | (simp only [RPOrig.iter_copy, RPRef.iter_copy, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.iter_copy RPRef.iter_copy RPOrig.iter_copy.loop RPRef.iter_copy.loop; rfl))
    | (simp only [RPOrig.iter_copy, RPRef.iter_copy, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.iter_copy RPRef.iter_copy RPOrig.iter_copy.loop RPRef.iter_copy.loop; rfl))
    | (simp only [RPOrig.iter_copy, RPRef.iter_copy, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.iter_copy RPRef.iter_copy RPOrig.iter_copy.loop RPRef.iter_copy.loop; rfl))
    | (simp only [RPOrig.iter_copy, RPRef.iter_copy]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.iter_copy RPRef.iter_copy RPOrig.iter_copy.loop RPRef.iter_copy.loop; rfl))

theorem rp_equiv_simp (s : Array Int) (h_precond : iter_copy_precond (s)) :
    RPOrig.iter_copy s h_precond = RPRef.iter_copy s h_precond := by
  first
    | (simp [RPOrig.iter_copy, RPRef.iter_copy, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.iter_copy RPRef.iter_copy RPOrig.iter_copy.loop RPRef.iter_copy.loop; rfl))
    | (simp [RPOrig.iter_copy, RPRef.iter_copy, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.iter_copy RPRef.iter_copy RPOrig.iter_copy.loop RPRef.iter_copy.loop; rfl))
    | (simp [RPOrig.iter_copy, RPRef.iter_copy, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.iter_copy RPRef.iter_copy RPOrig.iter_copy.loop RPRef.iter_copy.loop; rfl))
    | (simp [RPOrig.iter_copy, RPRef.iter_copy]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.iter_copy RPRef.iter_copy RPOrig.iter_copy.loop RPRef.iter_copy.loop; rfl))

theorem rp_equiv_ac_rfl (s : Array Int) (h_precond : iter_copy_precond (s)) :
    RPOrig.iter_copy s h_precond = RPRef.iter_copy s h_precond := by
  (try simp only [RPOrig.iter_copy, RPRef.iter_copy]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.iter_copy RPRef.iter_copy RPOrig.iter_copy.loop RPRef.iter_copy.loop; rfl))
