-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isSublist_precond (sub : List Int) (main : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def isSublist (sub : List Int) (main : List Int) (h_precond : isSublist_precond (sub) (main)) : Bool :=
  let subLen := sub.length
  let mainLen := main.length
  if subLen > mainLen then
    false
  else
    let rec check (i : Nat) : Bool :=
      if i + subLen > mainLen then
        false
      else if sub = (main.drop i).take subLen then
        true
      else if i + 1 ≤ mainLen then
        check (i + 1)
      else
        false
    termination_by mainLen - i
    check 0
end RPOrig

namespace RPRef

def isSublist (sub : List Int) (main : List Int) (h_precond : isSublist_precond (sub) (main)) : Bool :=
  let subLen := sub.length
  let mainLen := main.length
  if subLen > mainLen then
    false
  else
    let rec check (i : Nat) : Bool :=
      if i + subLen > mainLen then
        false
      else if sub = (main.drop i).take subLen then
        true
      else if 1 + i ≤ mainLen then
        check (i + 1)
      else
        false
    termination_by mainLen - i
    check 0
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (sub : List Int) (main : List Int) (h_precond : isSublist_precond (sub) (main)) :
    RPOrig.isSublist sub main h_precond = RPRef.isSublist sub main h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (sub : List Int) (main : List Int) (h_precond : isSublist_precond (sub) (main)) :
    RPOrig.isSublist sub main h_precond = RPRef.isSublist sub main h_precond := rfl

theorem rp_equiv_delta_rfl (sub : List Int) (main : List Int) (h_precond : isSublist_precond (sub) (main)) :
    RPOrig.isSublist sub main h_precond = RPRef.isSublist sub main h_precond := by
  delta RPOrig.isSublist RPRef.isSublist RPOrig.isSublist.check RPRef.isSublist.check
  rfl

theorem rp_equiv_simp_only (sub : List Int) (main : List Int) (h_precond : isSublist_precond (sub) (main)) :
    RPOrig.isSublist sub main h_precond = RPRef.isSublist sub main h_precond := by
  first
    | (simp only [RPOrig.isSublist, RPRef.isSublist, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isSublist RPRef.isSublist RPOrig.isSublist.check RPRef.isSublist.check; rfl))
    | (simp only [RPOrig.isSublist, RPRef.isSublist, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isSublist RPRef.isSublist RPOrig.isSublist.check RPRef.isSublist.check; rfl))
    | (simp only [RPOrig.isSublist, RPRef.isSublist, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isSublist RPRef.isSublist RPOrig.isSublist.check RPRef.isSublist.check; rfl))
    | (simp only [RPOrig.isSublist, RPRef.isSublist]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isSublist RPRef.isSublist RPOrig.isSublist.check RPRef.isSublist.check; rfl))

theorem rp_equiv_simp (sub : List Int) (main : List Int) (h_precond : isSublist_precond (sub) (main)) :
    RPOrig.isSublist sub main h_precond = RPRef.isSublist sub main h_precond := by
  first
    | (simp [RPOrig.isSublist, RPRef.isSublist, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isSublist RPRef.isSublist RPOrig.isSublist.check RPRef.isSublist.check; rfl))
    | (simp [RPOrig.isSublist, RPRef.isSublist, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isSublist RPRef.isSublist RPOrig.isSublist.check RPRef.isSublist.check; rfl))
    | (simp [RPOrig.isSublist, RPRef.isSublist, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isSublist RPRef.isSublist RPOrig.isSublist.check RPRef.isSublist.check; rfl))
    | (simp [RPOrig.isSublist, RPRef.isSublist]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isSublist RPRef.isSublist RPOrig.isSublist.check RPRef.isSublist.check; rfl))

theorem rp_equiv_ac_rfl (sub : List Int) (main : List Int) (h_precond : isSublist_precond (sub) (main)) :
    RPOrig.isSublist sub main h_precond = RPRef.isSublist sub main h_precond := by
  (try simp only [RPOrig.isSublist, RPRef.isSublist]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isSublist RPRef.isSublist RPOrig.isSublist.check RPRef.isSublist.check; rfl))
