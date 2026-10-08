-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def task_code_precond (sequence : List Int) : Prop :=
  -- !benchmark @start precond
  sequence.length > 0  -- At least one element must be selected
  -- !benchmark @end precond



namespace RPOrig

def task_code (sequence : List Int) (h_precond : task_code_precond (sequence)) : Int :=
  match sequence with
  | []      => 0  -- If no elements are provided (should not happen according to the problem)
  | x :: xs =>
      let (_, maxSoFar) :=
        xs.foldl (fun (acc : Int × Int) (x : Int) =>
          let (cur, maxSoFar) := acc
          let newCur := if cur + x >= x then cur + x else x
          let newMax := if maxSoFar >= newCur then maxSoFar else newCur
          (newCur, newMax)
        ) (x, x)
      maxSoFar
end RPOrig

namespace RPRef
private def task_code__rp_helper_2348297c (sequence : List Int) (h_precond : task_code_precond (sequence)) : Int :=
  match sequence with
  | []      => 0  -- If no elements are provided (should not happen according to the problem)
  | x :: xs =>
      let (_, maxSoFar) :=
        xs.foldl (fun (acc : Int × Int) (x : Int) =>
          let (cur, maxSoFar) := acc
          let newCur := if cur + x >= x then cur + x else x
          let newMax := if maxSoFar >= newCur then maxSoFar else newCur
          (newCur, newMax)
        ) (x, x)
      maxSoFar

def task_code (sequence : List Int) (h_precond : task_code_precond (sequence)) : Int :=
  task_code__rp_helper_2348297c sequence h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (sequence : List Int) (h_precond : task_code_precond (sequence)) :
    RPOrig.task_code sequence h_precond = RPRef.task_code sequence h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (sequence : List Int) (h_precond : task_code_precond (sequence)) :
    RPOrig.task_code sequence h_precond = RPRef.task_code sequence h_precond := rfl

theorem rp_equiv_delta_rfl (sequence : List Int) (h_precond : task_code_precond (sequence)) :
    RPOrig.task_code sequence h_precond = RPRef.task_code sequence h_precond := by
  delta RPOrig.task_code RPRef.task_code RPRef.task_code__rp_helper_2348297c
  rfl

theorem rp_equiv_simp_only (sequence : List Int) (h_precond : task_code_precond (sequence)) :
    RPOrig.task_code sequence h_precond = RPRef.task_code sequence h_precond := by
  (simp only [RPOrig.task_code, RPRef.task_code, RPRef.task_code__rp_helper_2348297c]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.task_code RPRef.task_code RPRef.task_code__rp_helper_2348297c; rfl))

theorem rp_equiv_simp (sequence : List Int) (h_precond : task_code_precond (sequence)) :
    RPOrig.task_code sequence h_precond = RPRef.task_code sequence h_precond := by
  (simp [RPOrig.task_code, RPRef.task_code, RPRef.task_code__rp_helper_2348297c]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.task_code RPRef.task_code RPRef.task_code__rp_helper_2348297c; rfl))
