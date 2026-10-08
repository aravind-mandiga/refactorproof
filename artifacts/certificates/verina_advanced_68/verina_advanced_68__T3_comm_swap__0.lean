-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def runLengthEncoder_precond (input : String) : Prop :=
  -- !benchmark @start precond
  input.all (fun c => ¬c.isDigit)  -- no digits allowed in input (ambiguous encoding)
  -- !benchmark @end precond



namespace RPOrig

def runLengthEncoder (input : String) (h_precond : runLengthEncoder_precond (input)) : String :=
  -- Convert string to character list
  let chars : String → List Char := fun s => s.data

  -- Check character equality
  let charEq : Char → Char → Bool := fun c1 c2 => c1 == c2

  -- Convert number to string
  let numToString : Nat → String := fun n =>
    let rec digits : Nat → List Char := fun n =>
      if n < 10 then
        [Char.ofNat (n + 48)]  -- ASCII '0' is 48
      else
        digits (n / 10) ++ [Char.ofNat (n % 10 + 48)]
    String.mk (digits n)

  -- Main encoding logic (fixed version)
  let rec encode : List Char → Option Char → Nat → String :=
    fun input currentChar count =>
      match input with
      | [] =>
        -- Process remaining characters
        match currentChar with
        | none => ""
        | some c => String.mk [c] ++ numToString count
      | c::rest =>
        match currentChar with
        | none => encode rest c 1
        | some c' =>
          if charEq c c' then
            encode rest c' (count + 1)
          else
            let currentPart := String.mk [c'] ++ numToString count
            currentPart ++ encode rest c 1

  -- Handle empty input
  if input.isEmpty then
    ""
  else
    let firstChar := (chars input).head?
    encode (chars input).tail firstChar 1
end RPOrig

namespace RPRef

def runLengthEncoder (input : String) (h_precond : runLengthEncoder_precond (input)) : String :=
  -- Convert string to character list
  let chars : String → List Char := fun s => s.data

  -- Check character equality
  let charEq : Char → Char → Bool := fun c1 c2 => c1 == c2

  -- Convert number to string
  let numToString : Nat → String := fun n =>
    let rec digits : Nat → List Char := fun n =>
      if n < 10 then
        [Char.ofNat (48 + n)]  -- ASCII '0' is 48
      else
        digits (n / 10) ++ [Char.ofNat (n % 10 + 48)]
    String.mk (digits n)

  -- Main encoding logic (fixed version)
  let rec encode : List Char → Option Char → Nat → String :=
    fun input currentChar count =>
      match input with
      | [] =>
        -- Process remaining characters
        match currentChar with
        | none => ""
        | some c => String.mk [c] ++ numToString count
      | c::rest =>
        match currentChar with
        | none => encode rest c 1
        | some c' =>
          if charEq c c' then
            encode rest c' (count + 1)
          else
            let currentPart := String.mk [c'] ++ numToString count
            currentPart ++ encode rest c 1

  -- Handle empty input
  if input.isEmpty then
    ""
  else
    let firstChar := (chars input).head?
    encode (chars input).tail firstChar 1
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (input : String) (h_precond : runLengthEncoder_precond (input)) :
    RPOrig.runLengthEncoder input h_precond = RPRef.runLengthEncoder input h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (input : String) (h_precond : runLengthEncoder_precond (input)) :
    RPOrig.runLengthEncoder input h_precond = RPRef.runLengthEncoder input h_precond := rfl

theorem rp_equiv_delta_rfl (input : String) (h_precond : runLengthEncoder_precond (input)) :
    RPOrig.runLengthEncoder input h_precond = RPRef.runLengthEncoder input h_precond := by
  delta RPOrig.runLengthEncoder RPRef.runLengthEncoder RPOrig.runLengthEncoder.digits RPOrig.runLengthEncoder.encode RPRef.runLengthEncoder.digits RPRef.runLengthEncoder.encode
  rfl

theorem rp_equiv_simp_only (input : String) (h_precond : runLengthEncoder_precond (input)) :
    RPOrig.runLengthEncoder input h_precond = RPRef.runLengthEncoder input h_precond := by
  first
    | (simp only [RPOrig.runLengthEncoder, RPRef.runLengthEncoder, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.runLengthEncoder RPRef.runLengthEncoder RPOrig.runLengthEncoder.digits RPOrig.runLengthEncoder.encode RPRef.runLengthEncoder.digits RPRef.runLengthEncoder.encode; rfl))
    | (simp only [RPOrig.runLengthEncoder, RPRef.runLengthEncoder, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.runLengthEncoder RPRef.runLengthEncoder RPOrig.runLengthEncoder.digits RPOrig.runLengthEncoder.encode RPRef.runLengthEncoder.digits RPRef.runLengthEncoder.encode; rfl))
    | (simp only [RPOrig.runLengthEncoder, RPRef.runLengthEncoder, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.runLengthEncoder RPRef.runLengthEncoder RPOrig.runLengthEncoder.digits RPOrig.runLengthEncoder.encode RPRef.runLengthEncoder.digits RPRef.runLengthEncoder.encode; rfl))
    | (simp only [RPOrig.runLengthEncoder, RPRef.runLengthEncoder]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.runLengthEncoder RPRef.runLengthEncoder RPOrig.runLengthEncoder.digits RPOrig.runLengthEncoder.encode RPRef.runLengthEncoder.digits RPRef.runLengthEncoder.encode; rfl))

theorem rp_equiv_simp (input : String) (h_precond : runLengthEncoder_precond (input)) :
    RPOrig.runLengthEncoder input h_precond = RPRef.runLengthEncoder input h_precond := by
  first
    | (simp [RPOrig.runLengthEncoder, RPRef.runLengthEncoder, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.runLengthEncoder RPRef.runLengthEncoder RPOrig.runLengthEncoder.digits RPOrig.runLengthEncoder.encode RPRef.runLengthEncoder.digits RPRef.runLengthEncoder.encode; rfl))
    | (simp [RPOrig.runLengthEncoder, RPRef.runLengthEncoder, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.runLengthEncoder RPRef.runLengthEncoder RPOrig.runLengthEncoder.digits RPOrig.runLengthEncoder.encode RPRef.runLengthEncoder.digits RPRef.runLengthEncoder.encode; rfl))
    | (simp [RPOrig.runLengthEncoder, RPRef.runLengthEncoder, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.runLengthEncoder RPRef.runLengthEncoder RPOrig.runLengthEncoder.digits RPOrig.runLengthEncoder.encode RPRef.runLengthEncoder.digits RPRef.runLengthEncoder.encode; rfl))
    | (simp [RPOrig.runLengthEncoder, RPRef.runLengthEncoder]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.runLengthEncoder RPRef.runLengthEncoder RPOrig.runLengthEncoder.digits RPOrig.runLengthEncoder.encode RPRef.runLengthEncoder.digits RPRef.runLengthEncoder.encode; rfl))

theorem rp_equiv_ac_rfl (input : String) (h_precond : runLengthEncoder_precond (input)) :
    RPOrig.runLengthEncoder input h_precond = RPRef.runLengthEncoder input h_precond := by
  (try simp only [RPOrig.runLengthEncoder, RPRef.runLengthEncoder]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.runLengthEncoder RPRef.runLengthEncoder RPOrig.runLengthEncoder.digits RPOrig.runLengthEncoder.encode RPRef.runLengthEncoder.digits RPRef.runLengthEncoder.encode; rfl))
