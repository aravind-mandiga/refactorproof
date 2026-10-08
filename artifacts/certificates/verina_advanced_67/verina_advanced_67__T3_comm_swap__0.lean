-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def runLengthEncode_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def runLengthEncode (s : String) (h_precond : runLengthEncode_precond (s)) : List (Char × Nat) :=
  let chars := s.data

  let rec encodeAux (acc : List (Char × Nat)) (rest : List Char) : List (Char × Nat) :=
    match rest with
    | [] => acc.reverse
    | h :: t =>
      match acc with
      | (ch, count) :: accTail =>
        if ch = h then
          encodeAux ((ch, count + 1) :: accTail) t
        else
          encodeAux ((h, 1) :: (ch, count) :: accTail) t
      | [] =>
        encodeAux ([(h, 1)]) t

  let encoded := encodeAux [] chars
  encoded
end RPOrig

namespace RPRef

def runLengthEncode (s : String) (h_precond : runLengthEncode_precond (s)) : List (Char × Nat) :=
  let chars := s.data

  let rec encodeAux (acc : List (Char × Nat)) (rest : List Char) : List (Char × Nat) :=
    match rest with
    | [] => acc.reverse
    | h :: t =>
      match acc with
      | (ch, count) :: accTail =>
        if ch = h then
          encodeAux ((ch, 1 + count) :: accTail) t
        else
          encodeAux ((h, 1) :: (ch, count) :: accTail) t
      | [] =>
        encodeAux ([(h, 1)]) t

  let encoded := encodeAux [] chars
  encoded
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (s : String) (h_precond : runLengthEncode_precond (s)) :
    RPOrig.runLengthEncode s h_precond = RPRef.runLengthEncode s h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (s : String) (h_precond : runLengthEncode_precond (s)) :
    RPOrig.runLengthEncode s h_precond = RPRef.runLengthEncode s h_precond := rfl

theorem rp_equiv_delta_rfl (s : String) (h_precond : runLengthEncode_precond (s)) :
    RPOrig.runLengthEncode s h_precond = RPRef.runLengthEncode s h_precond := by
  delta RPOrig.runLengthEncode RPRef.runLengthEncode RPOrig.runLengthEncode.encodeAux RPRef.runLengthEncode.encodeAux
  rfl

theorem rp_equiv_simp_only (s : String) (h_precond : runLengthEncode_precond (s)) :
    RPOrig.runLengthEncode s h_precond = RPRef.runLengthEncode s h_precond := by
  first
    | (simp only [RPOrig.runLengthEncode, RPRef.runLengthEncode, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.runLengthEncode RPRef.runLengthEncode RPOrig.runLengthEncode.encodeAux RPRef.runLengthEncode.encodeAux; rfl))
    | (simp only [RPOrig.runLengthEncode, RPRef.runLengthEncode, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.runLengthEncode RPRef.runLengthEncode RPOrig.runLengthEncode.encodeAux RPRef.runLengthEncode.encodeAux; rfl))
    | (simp only [RPOrig.runLengthEncode, RPRef.runLengthEncode, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.runLengthEncode RPRef.runLengthEncode RPOrig.runLengthEncode.encodeAux RPRef.runLengthEncode.encodeAux; rfl))
    | (simp only [RPOrig.runLengthEncode, RPRef.runLengthEncode]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.runLengthEncode RPRef.runLengthEncode RPOrig.runLengthEncode.encodeAux RPRef.runLengthEncode.encodeAux; rfl))

theorem rp_equiv_simp (s : String) (h_precond : runLengthEncode_precond (s)) :
    RPOrig.runLengthEncode s h_precond = RPRef.runLengthEncode s h_precond := by
  first
    | (simp [RPOrig.runLengthEncode, RPRef.runLengthEncode, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.runLengthEncode RPRef.runLengthEncode RPOrig.runLengthEncode.encodeAux RPRef.runLengthEncode.encodeAux; rfl))
    | (simp [RPOrig.runLengthEncode, RPRef.runLengthEncode, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.runLengthEncode RPRef.runLengthEncode RPOrig.runLengthEncode.encodeAux RPRef.runLengthEncode.encodeAux; rfl))
    | (simp [RPOrig.runLengthEncode, RPRef.runLengthEncode, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.runLengthEncode RPRef.runLengthEncode RPOrig.runLengthEncode.encodeAux RPRef.runLengthEncode.encodeAux; rfl))
    | (simp [RPOrig.runLengthEncode, RPRef.runLengthEncode]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.runLengthEncode RPRef.runLengthEncode RPOrig.runLengthEncode.encodeAux RPRef.runLengthEncode.encodeAux; rfl))

theorem rp_equiv_ac_rfl (s : String) (h_precond : runLengthEncode_precond (s)) :
    RPOrig.runLengthEncode s h_precond = RPRef.runLengthEncode s h_precond := by
  (try simp only [RPOrig.runLengthEncode, RPRef.runLengthEncode]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.runLengthEncode RPRef.runLengthEncode RPOrig.runLengthEncode.encodeAux RPRef.runLengthEncode.encodeAux; rfl))
