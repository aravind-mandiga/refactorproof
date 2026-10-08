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
private def runLengthEncoder__rp_helper_27ce3751 (input : String) (h_precond : runLengthEncoder_precond (input)) : String :=
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

def runLengthEncoder (input : String) (h_precond : runLengthEncoder_precond (input)) : String :=
  runLengthEncoder__rp_helper_27ce3751 input h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (input : String) (h_precond : runLengthEncoder_precond (input)) :
    RPOrig.runLengthEncoder input h_precond = RPRef.runLengthEncoder input h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (input : String) (h_precond : runLengthEncoder_precond (input)) :
    RPOrig.runLengthEncoder input h_precond = RPRef.runLengthEncoder input h_precond := rfl

theorem rp_equiv_delta_rfl (input : String) (h_precond : runLengthEncoder_precond (input)) :
    RPOrig.runLengthEncoder input h_precond = RPRef.runLengthEncoder input h_precond := by
  delta RPOrig.runLengthEncoder RPRef.runLengthEncoder RPRef.runLengthEncoder__rp_helper_27ce3751 RPOrig.runLengthEncoder.digits RPOrig.runLengthEncoder.encode RPRef.runLengthEncoder__rp_helper_27ce3751.digits RPRef.runLengthEncoder__rp_helper_27ce3751.encode
  rfl

theorem rp_equiv_simp_only (input : String) (h_precond : runLengthEncoder_precond (input)) :
    RPOrig.runLengthEncoder input h_precond = RPRef.runLengthEncoder input h_precond := by
  (simp only [RPOrig.runLengthEncoder, RPRef.runLengthEncoder, RPRef.runLengthEncoder__rp_helper_27ce3751]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.runLengthEncoder RPRef.runLengthEncoder RPRef.runLengthEncoder__rp_helper_27ce3751 RPOrig.runLengthEncoder.digits RPOrig.runLengthEncoder.encode RPRef.runLengthEncoder__rp_helper_27ce3751.digits RPRef.runLengthEncoder__rp_helper_27ce3751.encode; rfl))

theorem rp_equiv_simp (input : String) (h_precond : runLengthEncoder_precond (input)) :
    RPOrig.runLengthEncoder input h_precond = RPRef.runLengthEncoder input h_precond := by
  (simp [RPOrig.runLengthEncoder, RPRef.runLengthEncoder, RPRef.runLengthEncoder__rp_helper_27ce3751]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.runLengthEncoder RPRef.runLengthEncoder RPRef.runLengthEncoder__rp_helper_27ce3751 RPOrig.runLengthEncoder.digits RPOrig.runLengthEncoder.encode RPRef.runLengthEncoder__rp_helper_27ce3751.digits RPRef.runLengthEncoder__rp_helper_27ce3751.encode; rfl))
