-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def concat_precond (a : Array Int) (b : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def concat (a : Array Int) (b : Array Int) (h_precond : concat_precond (a) (b)) : Array Int :=
  let n := a.size + b.size
  let rec loop (i : Nat) (c : Array Int) : Array Int :=
    if i < n then
      let value := if i < a.size then a[i]! else b[i - a.size]!
      loop (i + 1) (c.set! i value)
    else
      c
  loop 0 (Array.mkArray n 0)
end RPOrig

namespace RPRef

def concat (a : Array Int) (b : Array Int) (h_precond : concat_precond (a) (b)) : Array Int :=
  let n := a.size + b.size
  let rec loop (i : Nat) (c : Array Int) : Array Int :=
    if i < n then
      let value := if i < a.size then a[i]! else b[i - a.size]!
      loop (1 + i) (c.set! i value)
    else
      c
  loop 0 (Array.mkArray n 0)
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (b : Array Int) (h_precond : concat_precond (a) (b)) :
    RPOrig.concat a b h_precond = RPRef.concat a b h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (b : Array Int) (h_precond : concat_precond (a) (b)) :
    RPOrig.concat a b h_precond = RPRef.concat a b h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (b : Array Int) (h_precond : concat_precond (a) (b)) :
    RPOrig.concat a b h_precond = RPRef.concat a b h_precond := by
  delta RPOrig.concat RPRef.concat RPOrig.concat.loop RPRef.concat.loop
  rfl

theorem rp_equiv_simp_only (a : Array Int) (b : Array Int) (h_precond : concat_precond (a) (b)) :
    RPOrig.concat a b h_precond = RPRef.concat a b h_precond := by
  first
    | (simp only [RPOrig.concat, RPRef.concat, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.concat RPRef.concat RPOrig.concat.loop RPRef.concat.loop; rfl))
    | (simp only [RPOrig.concat, RPRef.concat, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.concat RPRef.concat RPOrig.concat.loop RPRef.concat.loop; rfl))
    | (simp only [RPOrig.concat, RPRef.concat, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.concat RPRef.concat RPOrig.concat.loop RPRef.concat.loop; rfl))
    | (simp only [RPOrig.concat, RPRef.concat]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.concat RPRef.concat RPOrig.concat.loop RPRef.concat.loop; rfl))

theorem rp_equiv_simp (a : Array Int) (b : Array Int) (h_precond : concat_precond (a) (b)) :
    RPOrig.concat a b h_precond = RPRef.concat a b h_precond := by
  first
    | (simp [RPOrig.concat, RPRef.concat, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.concat RPRef.concat RPOrig.concat.loop RPRef.concat.loop; rfl))
    | (simp [RPOrig.concat, RPRef.concat, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.concat RPRef.concat RPOrig.concat.loop RPRef.concat.loop; rfl))
    | (simp [RPOrig.concat, RPRef.concat, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.concat RPRef.concat RPOrig.concat.loop RPRef.concat.loop; rfl))
    | (simp [RPOrig.concat, RPRef.concat]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.concat RPRef.concat RPOrig.concat.loop RPRef.concat.loop; rfl))

theorem rp_equiv_ac_rfl (a : Array Int) (b : Array Int) (h_precond : concat_precond (a) (b)) :
    RPOrig.concat a b h_precond = RPRef.concat a b h_precond := by
  (try simp only [RPOrig.concat, RPRef.concat]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.concat RPRef.concat RPOrig.concat.loop RPRef.concat.loop; rfl))
