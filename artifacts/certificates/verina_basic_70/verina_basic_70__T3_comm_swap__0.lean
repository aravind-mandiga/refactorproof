-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def LinearSearch3_precond (a : Array Int) (P : Int -> Bool) : Prop :=
  -- !benchmark @start precond
  ∃ i, i < a.size ∧ P (a[i]!)
  -- !benchmark @end precond



namespace RPOrig

def LinearSearch3 (a : Array Int) (P : Int -> Bool) (h_precond : LinearSearch3_precond (a) (P)) : Nat :=
  let rec loop (n : Nat) : Nat :=
    if n < a.size then
      if P (a[n]!) then n else loop (n + 1)
    else
      0
  loop 0
end RPOrig

namespace RPRef

def LinearSearch3 (a : Array Int) (P : Int -> Bool) (h_precond : LinearSearch3_precond (a) (P)) : Nat :=
  let rec loop (n : Nat) : Nat :=
    if n < a.size then
      if P (a[n]!) then n else loop (1 + n)
    else
      0
  loop 0
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (P : Int -> Bool) (h_precond : LinearSearch3_precond (a) (P)) :
    RPOrig.LinearSearch3 a P h_precond = RPRef.LinearSearch3 a P h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (P : Int -> Bool) (h_precond : LinearSearch3_precond (a) (P)) :
    RPOrig.LinearSearch3 a P h_precond = RPRef.LinearSearch3 a P h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (P : Int -> Bool) (h_precond : LinearSearch3_precond (a) (P)) :
    RPOrig.LinearSearch3 a P h_precond = RPRef.LinearSearch3 a P h_precond := by
  delta RPOrig.LinearSearch3 RPRef.LinearSearch3 RPOrig.LinearSearch3.loop RPRef.LinearSearch3.loop
  rfl

theorem rp_equiv_simp_only (a : Array Int) (P : Int -> Bool) (h_precond : LinearSearch3_precond (a) (P)) :
    RPOrig.LinearSearch3 a P h_precond = RPRef.LinearSearch3 a P h_precond := by
  first
    | (simp only [RPOrig.LinearSearch3, RPRef.LinearSearch3, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LinearSearch3 RPRef.LinearSearch3 RPOrig.LinearSearch3.loop RPRef.LinearSearch3.loop; rfl))
    | (simp only [RPOrig.LinearSearch3, RPRef.LinearSearch3, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LinearSearch3 RPRef.LinearSearch3 RPOrig.LinearSearch3.loop RPRef.LinearSearch3.loop; rfl))
    | (simp only [RPOrig.LinearSearch3, RPRef.LinearSearch3, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LinearSearch3 RPRef.LinearSearch3 RPOrig.LinearSearch3.loop RPRef.LinearSearch3.loop; rfl))
    | (simp only [RPOrig.LinearSearch3, RPRef.LinearSearch3]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LinearSearch3 RPRef.LinearSearch3 RPOrig.LinearSearch3.loop RPRef.LinearSearch3.loop; rfl))

theorem rp_equiv_simp (a : Array Int) (P : Int -> Bool) (h_precond : LinearSearch3_precond (a) (P)) :
    RPOrig.LinearSearch3 a P h_precond = RPRef.LinearSearch3 a P h_precond := by
  first
    | (simp [RPOrig.LinearSearch3, RPRef.LinearSearch3, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LinearSearch3 RPRef.LinearSearch3 RPOrig.LinearSearch3.loop RPRef.LinearSearch3.loop; rfl))
    | (simp [RPOrig.LinearSearch3, RPRef.LinearSearch3, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LinearSearch3 RPRef.LinearSearch3 RPOrig.LinearSearch3.loop RPRef.LinearSearch3.loop; rfl))
    | (simp [RPOrig.LinearSearch3, RPRef.LinearSearch3, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LinearSearch3 RPRef.LinearSearch3 RPOrig.LinearSearch3.loop RPRef.LinearSearch3.loop; rfl))
    | (simp [RPOrig.LinearSearch3, RPRef.LinearSearch3]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LinearSearch3 RPRef.LinearSearch3 RPOrig.LinearSearch3.loop RPRef.LinearSearch3.loop; rfl))

theorem rp_equiv_ac_rfl (a : Array Int) (P : Int -> Bool) (h_precond : LinearSearch3_precond (a) (P)) :
    RPOrig.LinearSearch3 a P h_precond = RPRef.LinearSearch3 a P h_precond := by
  (try simp only [RPOrig.LinearSearch3, RPRef.LinearSearch3]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LinearSearch3 RPRef.LinearSearch3 RPOrig.LinearSearch3.loop RPRef.LinearSearch3.loop; rfl))
