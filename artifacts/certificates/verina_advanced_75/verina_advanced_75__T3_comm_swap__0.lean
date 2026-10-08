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

def task_code (sequence : List Int) (h_precond : task_code_precond (sequence)) : Int :=
  match sequence with
  | []      => 0  -- If no elements are provided (should not happen according to the problem)
  | x :: xs =>
      let (_, maxSoFar) :=
        xs.foldl (fun (acc : Int × Int) (x : Int) =>
          let (cur, maxSoFar) := acc
          let newCur := if x + cur >= x then cur + x else x
          let newMax := if maxSoFar >= newCur then maxSoFar else newCur
          (newCur, newMax)
        ) (x, x)
      maxSoFar
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (sequence : List Int) (h_precond : task_code_precond (sequence)) :
    RPOrig.task_code sequence h_precond = RPRef.task_code sequence h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (sequence : List Int) (h_precond : task_code_precond (sequence)) :
    RPOrig.task_code sequence h_precond = RPRef.task_code sequence h_precond := rfl

theorem rp_equiv_delta_rfl (sequence : List Int) (h_precond : task_code_precond (sequence)) :
    RPOrig.task_code sequence h_precond = RPRef.task_code sequence h_precond := by
  delta RPOrig.task_code RPRef.task_code
  rfl

theorem rp_equiv_simp_only (sequence : List Int) (h_precond : task_code_precond (sequence)) :
    RPOrig.task_code sequence h_precond = RPRef.task_code sequence h_precond := by
  first
    | (simp only [RPOrig.task_code, RPRef.task_code, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.task_code RPRef.task_code; rfl))
    | (simp only [RPOrig.task_code, RPRef.task_code, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.task_code RPRef.task_code; rfl))
    | (simp only [RPOrig.task_code, RPRef.task_code, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.task_code RPRef.task_code; rfl))
    | (simp only [RPOrig.task_code, RPRef.task_code]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.task_code RPRef.task_code; rfl))

theorem rp_equiv_simp (sequence : List Int) (h_precond : task_code_precond (sequence)) :
    RPOrig.task_code sequence h_precond = RPRef.task_code sequence h_precond := by
  first
    | (simp [RPOrig.task_code, RPRef.task_code, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.task_code RPRef.task_code; rfl))
    | (simp [RPOrig.task_code, RPRef.task_code, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.task_code RPRef.task_code; rfl))
    | (simp [RPOrig.task_code, RPRef.task_code, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.task_code RPRef.task_code; rfl))
    | (simp [RPOrig.task_code, RPRef.task_code]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.task_code RPRef.task_code; rfl))

theorem rp_equiv_ac_rfl (sequence : List Int) (h_precond : task_code_precond (sequence)) :
    RPOrig.task_code sequence h_precond = RPRef.task_code sequence h_precond := by
  (try simp only [RPOrig.task_code, RPRef.task_code]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.task_code RPRef.task_code; rfl))
