-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def binaryToDecimal_precond (digits : List Nat) : Prop :=
  -- !benchmark @start precond
  digits.all (fun d => d = 0 ∨ d = 1)
  -- !benchmark @end precond



namespace RPOrig

def binaryToDecimal (digits : List Nat) (h_precond : binaryToDecimal_precond (digits)) : Nat :=
  let rec helper (digits : List Nat) : Nat :=
    match digits with
    | [] => 0
    | first :: rest => first * Nat.pow 2 rest.length + helper rest
  helper digits
end RPOrig

namespace RPRef

def binaryToDecimal (digits : List Nat) (h_precond : binaryToDecimal_precond (digits)) : Nat :=
  let __rp_tmp_1eadd343 : Nat :=
    let rec helper (digits : List Nat) : Nat :=
      match digits with
      | [] => 0
      | first :: rest => first * Nat.pow 2 rest.length + helper rest
    helper digits
  __rp_tmp_1eadd343
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (digits : List Nat) (h_precond : binaryToDecimal_precond (digits)) :
    RPOrig.binaryToDecimal digits h_precond = RPRef.binaryToDecimal digits h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (digits : List Nat) (h_precond : binaryToDecimal_precond (digits)) :
    RPOrig.binaryToDecimal digits h_precond = RPRef.binaryToDecimal digits h_precond := rfl

theorem rp_equiv_delta_rfl (digits : List Nat) (h_precond : binaryToDecimal_precond (digits)) :
    RPOrig.binaryToDecimal digits h_precond = RPRef.binaryToDecimal digits h_precond := by
  delta RPOrig.binaryToDecimal RPRef.binaryToDecimal RPOrig.binaryToDecimal.helper RPRef.binaryToDecimal.helper
  rfl

theorem rp_equiv_simp_only (digits : List Nat) (h_precond : binaryToDecimal_precond (digits)) :
    RPOrig.binaryToDecimal digits h_precond = RPRef.binaryToDecimal digits h_precond := by
  (simp only [RPOrig.binaryToDecimal, RPRef.binaryToDecimal]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.binaryToDecimal RPRef.binaryToDecimal RPOrig.binaryToDecimal.helper RPRef.binaryToDecimal.helper; rfl))

theorem rp_equiv_simp (digits : List Nat) (h_precond : binaryToDecimal_precond (digits)) :
    RPOrig.binaryToDecimal digits h_precond = RPRef.binaryToDecimal digits h_precond := by
  (simp [RPOrig.binaryToDecimal, RPRef.binaryToDecimal]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.binaryToDecimal RPRef.binaryToDecimal RPOrig.binaryToDecimal.helper RPRef.binaryToDecimal.helper; rfl))
