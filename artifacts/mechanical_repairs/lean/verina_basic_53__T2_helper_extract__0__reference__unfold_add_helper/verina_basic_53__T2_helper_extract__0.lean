-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def CalSum_precond (N : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

private def CalSum__rp_helper_f974fb52 (N : Nat) (h_precond : CalSum_precond (N)) : Nat :=
  let rec loop (n : Nat) : Nat :=
    if n = 0 then 0
    else n + loop (n - 1)
  loop N
-- !benchmark @end code_aux


def CalSum (N : Nat) (h_precond : CalSum_precond (N)) : Nat :=
  -- !benchmark @start code
  CalSum__rp_helper_f974fb52 N h_precond
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def CalSum_postcond (N : Nat) (result: Nat) (h_precond : CalSum_precond (N)) :=
  -- !benchmark @start postcond
  2 * result = N * (N + 1)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem CalSum_spec_satisfied (N: Nat) (h_precond : CalSum_precond (N)) :
    CalSum_postcond (N) (CalSum (N) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold CalSum_postcond CalSum CalSum__rp_helper_f974fb52
  induction N with
  | zero =>
    unfold CalSum.loop
    simp
  | succ n ih =>
    unfold CalSum_precond at ih
    simp at ih
    unfold CalSum.loop
    simp
    rw [Nat.mul_add]
    rw [ih]
    rw [← Nat.add_mul]
    rw [Nat.add_comm, Nat.mul_comm]
  -- !benchmark @end proof
