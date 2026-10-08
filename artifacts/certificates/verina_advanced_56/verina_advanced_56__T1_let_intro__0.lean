-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def moveZeroes_precond (xs : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
-- Count how many times a specific value appears in the list


namespace RPOrig

def moveZeroes (xs : List Int) (h_precond : moveZeroes_precond (xs)) : List Int :=
  let nonzeros := xs.filter (fun x => x ≠ 0)
  let zeros := xs.filter (fun x => x = 0)
  nonzeros ++ zeros
end RPOrig

namespace RPRef

def moveZeroes (xs : List Int) (h_precond : moveZeroes_precond (xs)) : List Int :=
  let __rp_tmp_69e72a79 : List Int :=
    let nonzeros := xs.filter (fun x => x ≠ 0)
    let zeros := xs.filter (fun x => x = 0)
    nonzeros ++ zeros
  __rp_tmp_69e72a79
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (xs : List Int) (h_precond : moveZeroes_precond (xs)) :
    RPOrig.moveZeroes xs h_precond = RPRef.moveZeroes xs h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (xs : List Int) (h_precond : moveZeroes_precond (xs)) :
    RPOrig.moveZeroes xs h_precond = RPRef.moveZeroes xs h_precond := rfl

theorem rp_equiv_delta_rfl (xs : List Int) (h_precond : moveZeroes_precond (xs)) :
    RPOrig.moveZeroes xs h_precond = RPRef.moveZeroes xs h_precond := by
  delta RPOrig.moveZeroes RPRef.moveZeroes
  rfl

theorem rp_equiv_simp_only (xs : List Int) (h_precond : moveZeroes_precond (xs)) :
    RPOrig.moveZeroes xs h_precond = RPRef.moveZeroes xs h_precond := by
  (simp only [RPOrig.moveZeroes, RPRef.moveZeroes]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.moveZeroes RPRef.moveZeroes; rfl))

theorem rp_equiv_simp (xs : List Int) (h_precond : moveZeroes_precond (xs)) :
    RPOrig.moveZeroes xs h_precond = RPRef.moveZeroes xs h_precond := by
  (simp [RPOrig.moveZeroes, RPRef.moveZeroes]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.moveZeroes RPRef.moveZeroes; rfl))
