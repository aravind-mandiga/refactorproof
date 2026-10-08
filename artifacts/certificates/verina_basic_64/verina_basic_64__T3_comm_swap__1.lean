-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def insert_precond (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) : Prop :=
  -- !benchmark @start precond
  l ≤ oline.size ∧
  p ≤ nl.size ∧
  atPos ≤ l
  -- !benchmark @end precond



namespace RPOrig

def insert (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) (h_precond : insert_precond (oline) (l) (nl) (p) (atPos)) : Array Char :=
  let result := Array.mkArray (l + p) ' '

  let result := Array.foldl
    (fun acc i =>
      if i < atPos then acc.set! i (oline[i]!) else acc)
    result
    (Array.range l)

  let result := Array.foldl
    (fun acc i =>
      acc.set! (atPos + i) (nl[i]!))
    result
    (Array.range p)

  let result := Array.foldl
    (fun acc i =>
      if i >= atPos then acc.set! (i + p) (oline[i]!) else acc)
    result
    (Array.range l)

  result
end RPOrig

namespace RPRef

def insert (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) (h_precond : insert_precond (oline) (l) (nl) (p) (atPos)) : Array Char :=
  let result := Array.mkArray (l + p) ' '

  let result := Array.foldl
    (fun acc i =>
      if i < atPos then acc.set! i (oline[i]!) else acc)
    result
    (Array.range l)

  let result := Array.foldl
    (fun acc i =>
      acc.set! (i + atPos) (nl[i]!))
    result
    (Array.range p)

  let result := Array.foldl
    (fun acc i =>
      if i >= atPos then acc.set! (i + p) (oline[i]!) else acc)
    result
    (Array.range l)

  result
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) (h_precond : insert_precond (oline) (l) (nl) (p) (atPos)) :
    RPOrig.insert oline l nl p atPos h_precond = RPRef.insert oline l nl p atPos h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) (h_precond : insert_precond (oline) (l) (nl) (p) (atPos)) :
    RPOrig.insert oline l nl p atPos h_precond = RPRef.insert oline l nl p atPos h_precond := rfl

theorem rp_equiv_delta_rfl (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) (h_precond : insert_precond (oline) (l) (nl) (p) (atPos)) :
    RPOrig.insert oline l nl p atPos h_precond = RPRef.insert oline l nl p atPos h_precond := by
  delta RPOrig.insert RPRef.insert
  rfl

theorem rp_equiv_simp_only (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) (h_precond : insert_precond (oline) (l) (nl) (p) (atPos)) :
    RPOrig.insert oline l nl p atPos h_precond = RPRef.insert oline l nl p atPos h_precond := by
  first
    | (simp only [RPOrig.insert, RPRef.insert, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.insert RPRef.insert; rfl))
    | (simp only [RPOrig.insert, RPRef.insert, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.insert RPRef.insert; rfl))
    | (simp only [RPOrig.insert, RPRef.insert, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.insert RPRef.insert; rfl))
    | (simp only [RPOrig.insert, RPRef.insert]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.insert RPRef.insert; rfl))

theorem rp_equiv_simp (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) (h_precond : insert_precond (oline) (l) (nl) (p) (atPos)) :
    RPOrig.insert oline l nl p atPos h_precond = RPRef.insert oline l nl p atPos h_precond := by
  first
    | (simp [RPOrig.insert, RPRef.insert, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.insert RPRef.insert; rfl))
    | (simp [RPOrig.insert, RPRef.insert, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.insert RPRef.insert; rfl))
    | (simp [RPOrig.insert, RPRef.insert, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.insert RPRef.insert; rfl))
    | (simp [RPOrig.insert, RPRef.insert]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.insert RPRef.insert; rfl))

theorem rp_equiv_ac_rfl (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) (h_precond : insert_precond (oline) (l) (nl) (p) (atPos)) :
    RPOrig.insert oline l nl p atPos h_precond = RPRef.insert oline l nl p atPos h_precond := by
  (try simp only [RPOrig.insert, RPRef.insert]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.insert RPRef.insert; rfl))
