-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def DoubleQuadruple_precond (x : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def DoubleQuadruple (x : Int) (h_precond : DoubleQuadruple_precond (x)) : (Int × Int) :=
  let a := 2 * x
  let b := 2 * a
  (a, b)
end RPOrig

namespace RPRef

def DoubleQuadruple (x : Int) (h_precond : DoubleQuadruple_precond (x)) : (Int × Int) :=
  let __rp_tmp_883fb5c3 : (Int × Int) :=
    let a := 2 * x
    let b := 2 * a
    (a, b)
  __rp_tmp_883fb5c3
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (x : Int) (h_precond : DoubleQuadruple_precond (x)) :
    RPOrig.DoubleQuadruple x h_precond = RPRef.DoubleQuadruple x h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (x : Int) (h_precond : DoubleQuadruple_precond (x)) :
    RPOrig.DoubleQuadruple x h_precond = RPRef.DoubleQuadruple x h_precond := rfl

theorem rp_equiv_delta_rfl (x : Int) (h_precond : DoubleQuadruple_precond (x)) :
    RPOrig.DoubleQuadruple x h_precond = RPRef.DoubleQuadruple x h_precond := by
  delta RPOrig.DoubleQuadruple RPRef.DoubleQuadruple
  rfl

theorem rp_equiv_simp_only (x : Int) (h_precond : DoubleQuadruple_precond (x)) :
    RPOrig.DoubleQuadruple x h_precond = RPRef.DoubleQuadruple x h_precond := by
  (simp only [RPOrig.DoubleQuadruple, RPRef.DoubleQuadruple]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.DoubleQuadruple RPRef.DoubleQuadruple; rfl))

theorem rp_equiv_simp (x : Int) (h_precond : DoubleQuadruple_precond (x)) :
    RPOrig.DoubleQuadruple x h_precond = RPRef.DoubleQuadruple x h_precond := by
  (simp [RPOrig.DoubleQuadruple, RPRef.DoubleQuadruple]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.DoubleQuadruple RPRef.DoubleQuadruple; rfl))
