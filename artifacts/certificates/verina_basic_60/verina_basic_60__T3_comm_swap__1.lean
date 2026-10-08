-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux
def isEven (n : Int) : Bool :=
  n % 2 = 0
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def FindEvenNumbers_precond (arr : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def FindEvenNumbers (arr : Array Int) (h_precond : FindEvenNumbers_precond (arr)) : Array Int :=
  let rec loop (i : Nat) (acc : Array Int) : Array Int :=
    if i < arr.size then
      if isEven (arr.getD i 0) then
        loop (i + 1) (acc.push (arr.getD i 0))
      else
        loop (i + 1) acc
    else
      acc
  loop 0 (Array.mkEmpty 0)
end RPOrig

namespace RPRef

def FindEvenNumbers (arr : Array Int) (h_precond : FindEvenNumbers_precond (arr)) : Array Int :=
  let rec loop (i : Nat) (acc : Array Int) : Array Int :=
    if i < arr.size then
      if isEven (arr.getD i 0) then
        loop (i + 1) (acc.push (arr.getD i 0))
      else
        loop (1 + i) acc
    else
      acc
  loop 0 (Array.mkEmpty 0)
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (arr : Array Int) (h_precond : FindEvenNumbers_precond (arr)) :
    RPOrig.FindEvenNumbers arr h_precond = RPRef.FindEvenNumbers arr h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (arr : Array Int) (h_precond : FindEvenNumbers_precond (arr)) :
    RPOrig.FindEvenNumbers arr h_precond = RPRef.FindEvenNumbers arr h_precond := rfl

theorem rp_equiv_delta_rfl (arr : Array Int) (h_precond : FindEvenNumbers_precond (arr)) :
    RPOrig.FindEvenNumbers arr h_precond = RPRef.FindEvenNumbers arr h_precond := by
  delta RPOrig.FindEvenNumbers RPRef.FindEvenNumbers RPOrig.FindEvenNumbers.loop RPRef.FindEvenNumbers.loop
  rfl

theorem rp_equiv_simp_only (arr : Array Int) (h_precond : FindEvenNumbers_precond (arr)) :
    RPOrig.FindEvenNumbers arr h_precond = RPRef.FindEvenNumbers arr h_precond := by
  first
    | (simp only [RPOrig.FindEvenNumbers, RPRef.FindEvenNumbers, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.FindEvenNumbers RPRef.FindEvenNumbers RPOrig.FindEvenNumbers.loop RPRef.FindEvenNumbers.loop; rfl))
    | (simp only [RPOrig.FindEvenNumbers, RPRef.FindEvenNumbers, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.FindEvenNumbers RPRef.FindEvenNumbers RPOrig.FindEvenNumbers.loop RPRef.FindEvenNumbers.loop; rfl))
    | (simp only [RPOrig.FindEvenNumbers, RPRef.FindEvenNumbers, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.FindEvenNumbers RPRef.FindEvenNumbers RPOrig.FindEvenNumbers.loop RPRef.FindEvenNumbers.loop; rfl))
    | (simp only [RPOrig.FindEvenNumbers, RPRef.FindEvenNumbers]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.FindEvenNumbers RPRef.FindEvenNumbers RPOrig.FindEvenNumbers.loop RPRef.FindEvenNumbers.loop; rfl))

theorem rp_equiv_simp (arr : Array Int) (h_precond : FindEvenNumbers_precond (arr)) :
    RPOrig.FindEvenNumbers arr h_precond = RPRef.FindEvenNumbers arr h_precond := by
  first
    | (simp [RPOrig.FindEvenNumbers, RPRef.FindEvenNumbers, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.FindEvenNumbers RPRef.FindEvenNumbers RPOrig.FindEvenNumbers.loop RPRef.FindEvenNumbers.loop; rfl))
    | (simp [RPOrig.FindEvenNumbers, RPRef.FindEvenNumbers, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.FindEvenNumbers RPRef.FindEvenNumbers RPOrig.FindEvenNumbers.loop RPRef.FindEvenNumbers.loop; rfl))
    | (simp [RPOrig.FindEvenNumbers, RPRef.FindEvenNumbers, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.FindEvenNumbers RPRef.FindEvenNumbers RPOrig.FindEvenNumbers.loop RPRef.FindEvenNumbers.loop; rfl))
    | (simp [RPOrig.FindEvenNumbers, RPRef.FindEvenNumbers]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.FindEvenNumbers RPRef.FindEvenNumbers RPOrig.FindEvenNumbers.loop RPRef.FindEvenNumbers.loop; rfl))

theorem rp_equiv_ac_rfl (arr : Array Int) (h_precond : FindEvenNumbers_precond (arr)) :
    RPOrig.FindEvenNumbers arr h_precond = RPRef.FindEvenNumbers arr h_precond := by
  (try simp only [RPOrig.FindEvenNumbers, RPRef.FindEvenNumbers]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.FindEvenNumbers RPRef.FindEvenNumbers RPOrig.FindEvenNumbers.loop RPRef.FindEvenNumbers.loop; rfl))
