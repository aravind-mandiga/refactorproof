-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isPrime_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  n ≥ 2
  -- !benchmark @end precond



namespace RPOrig

def isPrime (n : Nat) (h_precond : isPrime_precond (n)) : Bool :=
  let bound := n
  let rec check (i : Nat) (fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if i * i > n then true
    else if n % i = 0 then false
    else check (i + 1) (fuel - 1)
  check 2 bound
end RPOrig

namespace RPRef

def isPrime (n : Nat) (h_precond : isPrime_precond (n)) : Bool :=
  let bound := n
  let rec check (i : Nat) (fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if i * i > n then true
    else if n % i = 0 then false
    else check (1 + i) (fuel - 1)
  check 2 bound
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (n : Nat) (h_precond : isPrime_precond (n)) :
    RPOrig.isPrime n h_precond = RPRef.isPrime n h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (n : Nat) (h_precond : isPrime_precond (n)) :
    RPOrig.isPrime n h_precond = RPRef.isPrime n h_precond := rfl

theorem rp_equiv_delta_rfl (n : Nat) (h_precond : isPrime_precond (n)) :
    RPOrig.isPrime n h_precond = RPRef.isPrime n h_precond := by
  delta RPOrig.isPrime RPRef.isPrime RPOrig.isPrime.check RPRef.isPrime.check
  rfl

theorem rp_equiv_simp_only (n : Nat) (h_precond : isPrime_precond (n)) :
    RPOrig.isPrime n h_precond = RPRef.isPrime n h_precond := by
  first
    | (simp only [RPOrig.isPrime, RPRef.isPrime, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPrime RPRef.isPrime RPOrig.isPrime.check RPRef.isPrime.check; rfl))
    | (simp only [RPOrig.isPrime, RPRef.isPrime, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPrime RPRef.isPrime RPOrig.isPrime.check RPRef.isPrime.check; rfl))
    | (simp only [RPOrig.isPrime, RPRef.isPrime, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPrime RPRef.isPrime RPOrig.isPrime.check RPRef.isPrime.check; rfl))
    | (simp only [RPOrig.isPrime, RPRef.isPrime]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPrime RPRef.isPrime RPOrig.isPrime.check RPRef.isPrime.check; rfl))

theorem rp_equiv_simp (n : Nat) (h_precond : isPrime_precond (n)) :
    RPOrig.isPrime n h_precond = RPRef.isPrime n h_precond := by
  first
    | (simp [RPOrig.isPrime, RPRef.isPrime, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPrime RPRef.isPrime RPOrig.isPrime.check RPRef.isPrime.check; rfl))
    | (simp [RPOrig.isPrime, RPRef.isPrime, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPrime RPRef.isPrime RPOrig.isPrime.check RPRef.isPrime.check; rfl))
    | (simp [RPOrig.isPrime, RPRef.isPrime, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPrime RPRef.isPrime RPOrig.isPrime.check RPRef.isPrime.check; rfl))
    | (simp [RPOrig.isPrime, RPRef.isPrime]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPrime RPRef.isPrime RPOrig.isPrime.check RPRef.isPrime.check; rfl))

theorem rp_equiv_ac_rfl (n : Nat) (h_precond : isPrime_precond (n)) :
    RPOrig.isPrime n h_precond = RPRef.isPrime n h_precond := by
  (try simp only [RPOrig.isPrime, RPRef.isPrime]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPrime RPRef.isPrime RPOrig.isPrime.check RPRef.isPrime.check; rfl))
