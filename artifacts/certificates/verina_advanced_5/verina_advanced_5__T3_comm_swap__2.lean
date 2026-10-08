-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux
def listToNat : List Nat → Nat
| []       => 0
| d :: ds  => d + 10 * listToNat ds
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def addTwoNumbers_precond (l1 : List Nat) (l2 : List Nat) : Prop :=
  -- !benchmark @start precond
  l1.length > 0 ∧ l2.length > 0 ∧
  (∀ d ∈ l1, d < 10) ∧ (∀ d ∈ l2, d < 10) ∧
  (l1.getLast! ≠ 0 ∨ l1 = [0]) ∧
  (l2.getLast! ≠ 0 ∨ l2 = [0])
  -- !benchmark @end precond



namespace RPOrig

def addTwoNumbers (l1 : List Nat) (l2 : List Nat) (h_precond : addTwoNumbers_precond (l1) (l2)) : List Nat :=
  let rec addAux (l1 l2 : List Nat) (carry : Nat) : List Nat :=
    match l1, l2 with
    | [], [] =>
      if carry = 0 then [] else [carry]
    | h1::t1, [] =>
      let sum := h1 + carry
      (sum % 10) :: addAux t1 [] (sum / 10)
    | [], h2::t2 =>
      let sum := h2 + carry
      (sum % 10) :: addAux [] t2 (sum / 10)
    | h1::t1, h2::t2 =>
      let sum := h1 + h2 + carry
      (sum % 10) :: addAux t1 t2 (sum / 10)
  addAux l1 l2 0
end RPOrig

namespace RPRef

def addTwoNumbers (l1 : List Nat) (l2 : List Nat) (h_precond : addTwoNumbers_precond (l1) (l2)) : List Nat :=
  let rec addAux (l1 l2 : List Nat) (carry : Nat) : List Nat :=
    match l1, l2 with
    | [], [] =>
      if carry = 0 then [] else [carry]
    | h1::t1, [] =>
      let sum := h1 + carry
      (sum % 10) :: addAux t1 [] (sum / 10)
    | [], h2::t2 =>
      let sum := h2 + carry
      (sum % 10) :: addAux [] t2 (sum / 10)
    | h1::t1, h2::t2 =>
      let sum := h2 + h1 + carry
      (sum % 10) :: addAux t1 t2 (sum / 10)
  addAux l1 l2 0
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (l1 : List Nat) (l2 : List Nat) (h_precond : addTwoNumbers_precond (l1) (l2)) :
    RPOrig.addTwoNumbers l1 l2 h_precond = RPRef.addTwoNumbers l1 l2 h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (l1 : List Nat) (l2 : List Nat) (h_precond : addTwoNumbers_precond (l1) (l2)) :
    RPOrig.addTwoNumbers l1 l2 h_precond = RPRef.addTwoNumbers l1 l2 h_precond := rfl

theorem rp_equiv_delta_rfl (l1 : List Nat) (l2 : List Nat) (h_precond : addTwoNumbers_precond (l1) (l2)) :
    RPOrig.addTwoNumbers l1 l2 h_precond = RPRef.addTwoNumbers l1 l2 h_precond := by
  delta RPOrig.addTwoNumbers RPRef.addTwoNumbers RPOrig.addTwoNumbers.addAux RPRef.addTwoNumbers.addAux
  rfl

theorem rp_equiv_simp_only (l1 : List Nat) (l2 : List Nat) (h_precond : addTwoNumbers_precond (l1) (l2)) :
    RPOrig.addTwoNumbers l1 l2 h_precond = RPRef.addTwoNumbers l1 l2 h_precond := by
  first
    | (simp only [RPOrig.addTwoNumbers, RPRef.addTwoNumbers, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.addTwoNumbers RPRef.addTwoNumbers RPOrig.addTwoNumbers.addAux RPRef.addTwoNumbers.addAux; rfl))
    | (simp only [RPOrig.addTwoNumbers, RPRef.addTwoNumbers, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.addTwoNumbers RPRef.addTwoNumbers RPOrig.addTwoNumbers.addAux RPRef.addTwoNumbers.addAux; rfl))
    | (simp only [RPOrig.addTwoNumbers, RPRef.addTwoNumbers, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.addTwoNumbers RPRef.addTwoNumbers RPOrig.addTwoNumbers.addAux RPRef.addTwoNumbers.addAux; rfl))
    | (simp only [RPOrig.addTwoNumbers, RPRef.addTwoNumbers]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.addTwoNumbers RPRef.addTwoNumbers RPOrig.addTwoNumbers.addAux RPRef.addTwoNumbers.addAux; rfl))

theorem rp_equiv_simp (l1 : List Nat) (l2 : List Nat) (h_precond : addTwoNumbers_precond (l1) (l2)) :
    RPOrig.addTwoNumbers l1 l2 h_precond = RPRef.addTwoNumbers l1 l2 h_precond := by
  first
    | (simp [RPOrig.addTwoNumbers, RPRef.addTwoNumbers, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.addTwoNumbers RPRef.addTwoNumbers RPOrig.addTwoNumbers.addAux RPRef.addTwoNumbers.addAux; rfl))
    | (simp [RPOrig.addTwoNumbers, RPRef.addTwoNumbers, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.addTwoNumbers RPRef.addTwoNumbers RPOrig.addTwoNumbers.addAux RPRef.addTwoNumbers.addAux; rfl))
    | (simp [RPOrig.addTwoNumbers, RPRef.addTwoNumbers, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.addTwoNumbers RPRef.addTwoNumbers RPOrig.addTwoNumbers.addAux RPRef.addTwoNumbers.addAux; rfl))
    | (simp [RPOrig.addTwoNumbers, RPRef.addTwoNumbers]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.addTwoNumbers RPRef.addTwoNumbers RPOrig.addTwoNumbers.addAux RPRef.addTwoNumbers.addAux; rfl))

theorem rp_equiv_ac_rfl (l1 : List Nat) (l2 : List Nat) (h_precond : addTwoNumbers_precond (l1) (l2)) :
    RPOrig.addTwoNumbers l1 l2 h_precond = RPRef.addTwoNumbers l1 l2 h_precond := by
  (try simp only [RPOrig.addTwoNumbers, RPRef.addTwoNumbers]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.addTwoNumbers RPRef.addTwoNumbers RPOrig.addTwoNumbers.addAux RPRef.addTwoNumbers.addAux; rfl))
