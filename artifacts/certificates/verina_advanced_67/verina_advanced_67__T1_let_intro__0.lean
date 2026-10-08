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
  let __rp_tmp_ec3515e2 : List (Char × Nat) :=
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
  __rp_tmp_ec3515e2
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
  (simp only [RPOrig.runLengthEncode, RPRef.runLengthEncode]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.runLengthEncode RPRef.runLengthEncode RPOrig.runLengthEncode.encodeAux RPRef.runLengthEncode.encodeAux; rfl))

theorem rp_equiv_simp (s : String) (h_precond : runLengthEncode_precond (s)) :
    RPOrig.runLengthEncode s h_precond = RPRef.runLengthEncode s h_precond := by
  (simp [RPOrig.runLengthEncode, RPRef.runLengthEncode]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.runLengthEncode RPRef.runLengthEncode RPOrig.runLengthEncode.encodeAux RPRef.runLengthEncode.encodeAux; rfl))
