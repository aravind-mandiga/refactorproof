-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def containsZ_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def containsZ (s : String) (h_precond : containsZ_precond (s)) : Bool :=
  s.toList.any fun c => c = 'z' || c = 'Z'
end RPOrig

namespace RPRef

def containsZ (s : String) (h_precond : containsZ_precond (s)) : Bool :=
  let __rp_tmp_70a11263 : Bool :=
    s.toList.any fun c => c = 'z' || c = 'Z'
  __rp_tmp_70a11263
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (s : String) (h_precond : containsZ_precond (s)) :
    RPOrig.containsZ s h_precond = RPRef.containsZ s h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (s : String) (h_precond : containsZ_precond (s)) :
    RPOrig.containsZ s h_precond = RPRef.containsZ s h_precond := rfl

theorem rp_equiv_delta_rfl (s : String) (h_precond : containsZ_precond (s)) :
    RPOrig.containsZ s h_precond = RPRef.containsZ s h_precond := by
  delta RPOrig.containsZ RPRef.containsZ
  rfl

theorem rp_equiv_simp_only (s : String) (h_precond : containsZ_precond (s)) :
    RPOrig.containsZ s h_precond = RPRef.containsZ s h_precond := by
  (simp only [RPOrig.containsZ, RPRef.containsZ]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.containsZ RPRef.containsZ; rfl))

theorem rp_equiv_simp (s : String) (h_precond : containsZ_precond (s)) :
    RPOrig.containsZ s h_precond = RPRef.containsZ s h_precond := by
  (simp [RPOrig.containsZ, RPRef.containsZ]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.containsZ RPRef.containsZ; rfl))
