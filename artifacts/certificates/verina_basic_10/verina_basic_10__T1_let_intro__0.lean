-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isGreater_precond (n : Int) (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0
  -- !benchmark @end precond



namespace RPOrig

def isGreater (n : Int) (a : Array Int) (h_precond : isGreater_precond (n) (a)) : Bool :=
  a.all fun x => n > x
end RPOrig

namespace RPRef

def isGreater (n : Int) (a : Array Int) (h_precond : isGreater_precond (n) (a)) : Bool :=
  let __rp_tmp_f0724323 : Bool :=
    a.all fun x => n > x
  __rp_tmp_f0724323
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (n : Int) (a : Array Int) (h_precond : isGreater_precond (n) (a)) :
    RPOrig.isGreater n a h_precond = RPRef.isGreater n a h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (n : Int) (a : Array Int) (h_precond : isGreater_precond (n) (a)) :
    RPOrig.isGreater n a h_precond = RPRef.isGreater n a h_precond := rfl

theorem rp_equiv_delta_rfl (n : Int) (a : Array Int) (h_precond : isGreater_precond (n) (a)) :
    RPOrig.isGreater n a h_precond = RPRef.isGreater n a h_precond := by
  delta RPOrig.isGreater RPRef.isGreater
  rfl

theorem rp_equiv_simp_only (n : Int) (a : Array Int) (h_precond : isGreater_precond (n) (a)) :
    RPOrig.isGreater n a h_precond = RPRef.isGreater n a h_precond := by
  (simp only [RPOrig.isGreater, RPRef.isGreater]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isGreater RPRef.isGreater; rfl))

theorem rp_equiv_simp (n : Int) (a : Array Int) (h_precond : isGreater_precond (n) (a)) :
    RPOrig.isGreater n a h_precond = RPRef.isGreater n a h_precond := by
  (simp [RPOrig.isGreater, RPRef.isGreater]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isGreater RPRef.isGreater; rfl))
