-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def replace_precond (arr : Array Int) (k : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def replace_loop (oldArr : Array Int) (k : Int) : Nat → Array Int → Array Int
| i, acc =>
  if i < oldArr.size then
    if (oldArr[i]!) > k then
      replace_loop oldArr k (i+1) (acc.set! i (-1))
    else
      replace_loop oldArr k (i+1) acc
  else
    acc

namespace RPOrig

def replace (arr : Array Int) (k : Int) (h_precond : replace_precond (arr) (k)) : Array Int :=
  replace_loop arr k 0 arr
end RPOrig

namespace RPRef

private def replace__rp_helper_94d9cf8d (arr : Array Int) (k : Int) (h_precond : replace_precond (arr) (k)) : Array Int :=
  replace_loop arr k 0 arr

def replace (arr : Array Int) (k : Int) (h_precond : replace_precond (arr) (k)) : Array Int :=
  replace__rp_helper_94d9cf8d arr k h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (arr : Array Int) (k : Int) (h_precond : replace_precond (arr) (k)) :
    RPOrig.replace arr k h_precond = RPRef.replace arr k h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (arr : Array Int) (k : Int) (h_precond : replace_precond (arr) (k)) :
    RPOrig.replace arr k h_precond = RPRef.replace arr k h_precond := rfl

theorem rp_equiv_delta_rfl (arr : Array Int) (k : Int) (h_precond : replace_precond (arr) (k)) :
    RPOrig.replace arr k h_precond = RPRef.replace arr k h_precond := by
  delta RPOrig.replace RPRef.replace RPRef.replace__rp_helper_94d9cf8d
  rfl

theorem rp_equiv_simp_only (arr : Array Int) (k : Int) (h_precond : replace_precond (arr) (k)) :
    RPOrig.replace arr k h_precond = RPRef.replace arr k h_precond := by
  (simp only [RPOrig.replace, RPRef.replace, RPRef.replace__rp_helper_94d9cf8d]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.replace RPRef.replace RPRef.replace__rp_helper_94d9cf8d; rfl))

theorem rp_equiv_simp (arr : Array Int) (k : Int) (h_precond : replace_precond (arr) (k)) :
    RPOrig.replace arr k h_precond = RPRef.replace arr k h_precond := by
  (simp [RPOrig.replace, RPRef.replace, RPRef.replace__rp_helper_94d9cf8d]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.replace RPRef.replace RPRef.replace__rp_helper_94d9cf8d; rfl))
