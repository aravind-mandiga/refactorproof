-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def ComputeAvg_precond (a : Int) (b : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def ComputeAvg (a : Int) (b : Int) (h_precond : ComputeAvg_precond (a) (b)) : Int :=
  (a + b) / 2
end RPOrig

namespace RPRef

def ComputeAvg (a : Int) (b : Int) (h_precond : ComputeAvg_precond (a) (b)) : Int :=
  (b + a) / 2
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Int) (b : Int) (h_precond : ComputeAvg_precond (a) (b)) :
    RPOrig.ComputeAvg a b h_precond = RPRef.ComputeAvg a b h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Int) (b : Int) (h_precond : ComputeAvg_precond (a) (b)) :
    RPOrig.ComputeAvg a b h_precond = RPRef.ComputeAvg a b h_precond := rfl

theorem rp_equiv_delta_rfl (a : Int) (b : Int) (h_precond : ComputeAvg_precond (a) (b)) :
    RPOrig.ComputeAvg a b h_precond = RPRef.ComputeAvg a b h_precond := by
  delta RPOrig.ComputeAvg RPRef.ComputeAvg
  rfl

theorem rp_equiv_simp_only (a : Int) (b : Int) (h_precond : ComputeAvg_precond (a) (b)) :
    RPOrig.ComputeAvg a b h_precond = RPRef.ComputeAvg a b h_precond := by
  first
    | (simp only [RPOrig.ComputeAvg, RPRef.ComputeAvg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.ComputeAvg RPRef.ComputeAvg; rfl))
    | (simp only [RPOrig.ComputeAvg, RPRef.ComputeAvg, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.ComputeAvg RPRef.ComputeAvg; rfl))
    | (simp only [RPOrig.ComputeAvg, RPRef.ComputeAvg, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.ComputeAvg RPRef.ComputeAvg; rfl))
    | (simp only [RPOrig.ComputeAvg, RPRef.ComputeAvg]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.ComputeAvg RPRef.ComputeAvg; rfl))

theorem rp_equiv_simp (a : Int) (b : Int) (h_precond : ComputeAvg_precond (a) (b)) :
    RPOrig.ComputeAvg a b h_precond = RPRef.ComputeAvg a b h_precond := by
  first
    | (simp [RPOrig.ComputeAvg, RPRef.ComputeAvg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.ComputeAvg RPRef.ComputeAvg; rfl))
    | (simp [RPOrig.ComputeAvg, RPRef.ComputeAvg, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.ComputeAvg RPRef.ComputeAvg; rfl))
    | (simp [RPOrig.ComputeAvg, RPRef.ComputeAvg, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.ComputeAvg RPRef.ComputeAvg; rfl))
    | (simp [RPOrig.ComputeAvg, RPRef.ComputeAvg]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.ComputeAvg RPRef.ComputeAvg; rfl))

theorem rp_equiv_ac_rfl (a : Int) (b : Int) (h_precond : ComputeAvg_precond (a) (b)) :
    RPOrig.ComputeAvg a b h_precond = RPRef.ComputeAvg a b h_precond := by
  (try simp only [RPOrig.ComputeAvg, RPRef.ComputeAvg]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.ComputeAvg RPRef.ComputeAvg; rfl))
