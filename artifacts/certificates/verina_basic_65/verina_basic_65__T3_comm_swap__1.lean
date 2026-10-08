-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def SquareRoot_precond (N : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def SquareRoot (N : Nat) (h_precond : SquareRoot_precond (N)) : Nat :=
  let rec boundedLoop : Nat → Nat → Nat
    | 0, r => r
    | bound+1, r =>
        if (r + 1) * (r + 1) ≤ N then
          boundedLoop bound (r + 1)
        else
          r
  boundedLoop (N+1) 0
end RPOrig

namespace RPRef

def SquareRoot (N : Nat) (h_precond : SquareRoot_precond (N)) : Nat :=
  let rec boundedLoop : Nat → Nat → Nat
    | 0, r => r
    | bound+1, r =>
        if (r + 1) * (1 + r) ≤ N then
          boundedLoop bound (r + 1)
        else
          r
  boundedLoop (N+1) 0
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (N : Nat) (h_precond : SquareRoot_precond (N)) :
    RPOrig.SquareRoot N h_precond = RPRef.SquareRoot N h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (N : Nat) (h_precond : SquareRoot_precond (N)) :
    RPOrig.SquareRoot N h_precond = RPRef.SquareRoot N h_precond := rfl

theorem rp_equiv_delta_rfl (N : Nat) (h_precond : SquareRoot_precond (N)) :
    RPOrig.SquareRoot N h_precond = RPRef.SquareRoot N h_precond := by
  delta RPOrig.SquareRoot RPRef.SquareRoot RPOrig.SquareRoot.boundedLoop RPRef.SquareRoot.boundedLoop
  rfl

theorem rp_equiv_simp_only (N : Nat) (h_precond : SquareRoot_precond (N)) :
    RPOrig.SquareRoot N h_precond = RPRef.SquareRoot N h_precond := by
  first
    | (simp only [RPOrig.SquareRoot, RPRef.SquareRoot, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SquareRoot RPRef.SquareRoot RPOrig.SquareRoot.boundedLoop RPRef.SquareRoot.boundedLoop; rfl))
    | (simp only [RPOrig.SquareRoot, RPRef.SquareRoot, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SquareRoot RPRef.SquareRoot RPOrig.SquareRoot.boundedLoop RPRef.SquareRoot.boundedLoop; rfl))
    | (simp only [RPOrig.SquareRoot, RPRef.SquareRoot, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SquareRoot RPRef.SquareRoot RPOrig.SquareRoot.boundedLoop RPRef.SquareRoot.boundedLoop; rfl))
    | (simp only [RPOrig.SquareRoot, RPRef.SquareRoot]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SquareRoot RPRef.SquareRoot RPOrig.SquareRoot.boundedLoop RPRef.SquareRoot.boundedLoop; rfl))

theorem rp_equiv_simp (N : Nat) (h_precond : SquareRoot_precond (N)) :
    RPOrig.SquareRoot N h_precond = RPRef.SquareRoot N h_precond := by
  first
    | (simp [RPOrig.SquareRoot, RPRef.SquareRoot, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SquareRoot RPRef.SquareRoot RPOrig.SquareRoot.boundedLoop RPRef.SquareRoot.boundedLoop; rfl))
    | (simp [RPOrig.SquareRoot, RPRef.SquareRoot, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SquareRoot RPRef.SquareRoot RPOrig.SquareRoot.boundedLoop RPRef.SquareRoot.boundedLoop; rfl))
    | (simp [RPOrig.SquareRoot, RPRef.SquareRoot, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SquareRoot RPRef.SquareRoot RPOrig.SquareRoot.boundedLoop RPRef.SquareRoot.boundedLoop; rfl))
    | (simp [RPOrig.SquareRoot, RPRef.SquareRoot]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SquareRoot RPRef.SquareRoot RPOrig.SquareRoot.boundedLoop RPRef.SquareRoot.boundedLoop; rfl))

theorem rp_equiv_ac_rfl (N : Nat) (h_precond : SquareRoot_precond (N)) :
    RPOrig.SquareRoot N h_precond = RPRef.SquareRoot N h_precond := by
  (try simp only [RPOrig.SquareRoot, RPRef.SquareRoot]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SquareRoot RPRef.SquareRoot RPOrig.SquareRoot.boundedLoop RPRef.SquareRoot.boundedLoop; rfl))
