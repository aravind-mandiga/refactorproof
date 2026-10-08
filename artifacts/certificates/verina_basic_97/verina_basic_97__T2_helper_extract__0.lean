-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def TestArrayElements_precond (a : Array Int) (j : Nat) : Prop :=
  -- !benchmark @start precond
  j < a.size
  -- !benchmark @end precond



namespace RPOrig

def TestArrayElements (a : Array Int) (j : Nat) (h_precond : TestArrayElements_precond (a) (j)) : Array Int :=
  a.set! j 60
end RPOrig

namespace RPRef
private def TestArrayElements__rp_helper_9bca1c3a (a : Array Int) (j : Nat) (h_precond : TestArrayElements_precond (a) (j)) : Array Int :=
  a.set! j 60

def TestArrayElements (a : Array Int) (j : Nat) (h_precond : TestArrayElements_precond (a) (j)) : Array Int :=
  TestArrayElements__rp_helper_9bca1c3a a j h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (j : Nat) (h_precond : TestArrayElements_precond (a) (j)) :
    RPOrig.TestArrayElements a j h_precond = RPRef.TestArrayElements a j h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (j : Nat) (h_precond : TestArrayElements_precond (a) (j)) :
    RPOrig.TestArrayElements a j h_precond = RPRef.TestArrayElements a j h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (j : Nat) (h_precond : TestArrayElements_precond (a) (j)) :
    RPOrig.TestArrayElements a j h_precond = RPRef.TestArrayElements a j h_precond := by
  delta RPOrig.TestArrayElements RPRef.TestArrayElements RPRef.TestArrayElements__rp_helper_9bca1c3a
  rfl

theorem rp_equiv_simp_only (a : Array Int) (j : Nat) (h_precond : TestArrayElements_precond (a) (j)) :
    RPOrig.TestArrayElements a j h_precond = RPRef.TestArrayElements a j h_precond := by
  (simp only [RPOrig.TestArrayElements, RPRef.TestArrayElements, RPRef.TestArrayElements__rp_helper_9bca1c3a]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.TestArrayElements RPRef.TestArrayElements RPRef.TestArrayElements__rp_helper_9bca1c3a; rfl))

theorem rp_equiv_simp (a : Array Int) (j : Nat) (h_precond : TestArrayElements_precond (a) (j)) :
    RPOrig.TestArrayElements a j h_precond = RPRef.TestArrayElements a j h_precond := by
  (simp [RPOrig.TestArrayElements, RPRef.TestArrayElements, RPRef.TestArrayElements__rp_helper_9bca1c3a]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.TestArrayElements RPRef.TestArrayElements RPRef.TestArrayElements__rp_helper_9bca1c3a; rfl))
