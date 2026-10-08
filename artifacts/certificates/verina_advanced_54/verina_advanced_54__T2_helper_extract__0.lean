-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def missingNumber_precond (nums : List Nat) : Prop :=
  -- !benchmark @start precond
  nums.all (fun x => x ≤ nums.length) ∧ List.Nodup nums
  -- !benchmark @end precond



namespace RPOrig

def missingNumber (nums : List Nat) (h_precond : missingNumber_precond (nums)) : Nat :=
  let n := nums.length
  let expectedSum := (n * (n + 1)) / 2
  let actualSum := nums.foldl (· + ·) 0
  expectedSum - actualSum
end RPOrig

namespace RPRef
private def missingNumber__rp_helper_d60eb0e8 (nums : List Nat) (h_precond : missingNumber_precond (nums)) : Nat :=
  let n := nums.length
  let expectedSum := (n * (n + 1)) / 2
  let actualSum := nums.foldl (· + ·) 0
  expectedSum - actualSum

def missingNumber (nums : List Nat) (h_precond : missingNumber_precond (nums)) : Nat :=
  missingNumber__rp_helper_d60eb0e8 nums h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (nums : List Nat) (h_precond : missingNumber_precond (nums)) :
    RPOrig.missingNumber nums h_precond = RPRef.missingNumber nums h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (nums : List Nat) (h_precond : missingNumber_precond (nums)) :
    RPOrig.missingNumber nums h_precond = RPRef.missingNumber nums h_precond := rfl

theorem rp_equiv_delta_rfl (nums : List Nat) (h_precond : missingNumber_precond (nums)) :
    RPOrig.missingNumber nums h_precond = RPRef.missingNumber nums h_precond := by
  delta RPOrig.missingNumber RPRef.missingNumber RPRef.missingNumber__rp_helper_d60eb0e8
  rfl

theorem rp_equiv_simp_only (nums : List Nat) (h_precond : missingNumber_precond (nums)) :
    RPOrig.missingNumber nums h_precond = RPRef.missingNumber nums h_precond := by
  (simp only [RPOrig.missingNumber, RPRef.missingNumber, RPRef.missingNumber__rp_helper_d60eb0e8]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.missingNumber RPRef.missingNumber RPRef.missingNumber__rp_helper_d60eb0e8; rfl))

theorem rp_equiv_simp (nums : List Nat) (h_precond : missingNumber_precond (nums)) :
    RPOrig.missingNumber nums h_precond = RPRef.missingNumber nums h_precond := by
  (simp [RPOrig.missingNumber, RPRef.missingNumber, RPRef.missingNumber__rp_helper_d60eb0e8]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.missingNumber RPRef.missingNumber RPRef.missingNumber__rp_helper_d60eb0e8; rfl))
