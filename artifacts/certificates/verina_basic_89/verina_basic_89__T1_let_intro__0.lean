-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def SetToSeq_precond (s : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def SetToSeq (s : List Int) (h_precond : SetToSeq_precond (s)) : List Int :=
  s.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []
end RPOrig

namespace RPRef

def SetToSeq (s : List Int) (h_precond : SetToSeq_precond (s)) : List Int :=
  let __rp_tmp_9ad33ccb : List Int :=
    s.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []
  __rp_tmp_9ad33ccb
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (s : List Int) (h_precond : SetToSeq_precond (s)) :
    RPOrig.SetToSeq s h_precond = RPRef.SetToSeq s h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (s : List Int) (h_precond : SetToSeq_precond (s)) :
    RPOrig.SetToSeq s h_precond = RPRef.SetToSeq s h_precond := rfl

theorem rp_equiv_delta_rfl (s : List Int) (h_precond : SetToSeq_precond (s)) :
    RPOrig.SetToSeq s h_precond = RPRef.SetToSeq s h_precond := by
  delta RPOrig.SetToSeq RPRef.SetToSeq
  rfl

theorem rp_equiv_simp_only (s : List Int) (h_precond : SetToSeq_precond (s)) :
    RPOrig.SetToSeq s h_precond = RPRef.SetToSeq s h_precond := by
  (simp only [RPOrig.SetToSeq, RPRef.SetToSeq]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SetToSeq RPRef.SetToSeq; rfl))

theorem rp_equiv_simp (s : List Int) (h_precond : SetToSeq_precond (s)) :
    RPOrig.SetToSeq s h_precond = RPRef.SetToSeq s h_precond := by
  (simp [RPOrig.SetToSeq, RPRef.SetToSeq]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SetToSeq RPRef.SetToSeq; rfl))
