-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def Find_precond (a : Array Int) (key : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def Find (a : Array Int) (key : Int) (h_precond : Find_precond (a) (key)) : Int :=
  let rec search (index : Nat) : Int :=
    if index < a.size then
      if a[index]! = key then Int.ofNat index
      else search (index + 1)
    else -1
  search 0
end RPOrig

namespace RPRef

def Find (a : Array Int) (key : Int) (h_precond : Find_precond (a) (key)) : Int :=
  let rec search (index : Nat) : Int :=
    if index < a.size then
      if a[index]! = key then Int.ofNat index
      else search (1 + index)
    else -1
  search 0
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (key : Int) (h_precond : Find_precond (a) (key)) :
    RPOrig.Find a key h_precond = RPRef.Find a key h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (key : Int) (h_precond : Find_precond (a) (key)) :
    RPOrig.Find a key h_precond = RPRef.Find a key h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (key : Int) (h_precond : Find_precond (a) (key)) :
    RPOrig.Find a key h_precond = RPRef.Find a key h_precond := by
  delta RPOrig.Find RPRef.Find RPOrig.Find.search RPRef.Find.search
  rfl

theorem rp_equiv_simp_only (a : Array Int) (key : Int) (h_precond : Find_precond (a) (key)) :
    RPOrig.Find a key h_precond = RPRef.Find a key h_precond := by
  first
    | (simp only [RPOrig.Find, RPRef.Find, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Find RPRef.Find RPOrig.Find.search RPRef.Find.search; rfl))
    | (simp only [RPOrig.Find, RPRef.Find, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Find RPRef.Find RPOrig.Find.search RPRef.Find.search; rfl))
    | (simp only [RPOrig.Find, RPRef.Find, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Find RPRef.Find RPOrig.Find.search RPRef.Find.search; rfl))
    | (simp only [RPOrig.Find, RPRef.Find]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Find RPRef.Find RPOrig.Find.search RPRef.Find.search; rfl))

theorem rp_equiv_simp (a : Array Int) (key : Int) (h_precond : Find_precond (a) (key)) :
    RPOrig.Find a key h_precond = RPRef.Find a key h_precond := by
  first
    | (simp [RPOrig.Find, RPRef.Find, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Find RPRef.Find RPOrig.Find.search RPRef.Find.search; rfl))
    | (simp [RPOrig.Find, RPRef.Find, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Find RPRef.Find RPOrig.Find.search RPRef.Find.search; rfl))
    | (simp [RPOrig.Find, RPRef.Find, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Find RPRef.Find RPOrig.Find.search RPRef.Find.search; rfl))
    | (simp [RPOrig.Find, RPRef.Find]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Find RPRef.Find RPOrig.Find.search RPRef.Find.search; rfl))

theorem rp_equiv_ac_rfl (a : Array Int) (key : Int) (h_precond : Find_precond (a) (key)) :
    RPOrig.Find a key h_precond = RPRef.Find a key h_precond := by
  (try simp only [RPOrig.Find, RPRef.Find]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Find RPRef.Find RPOrig.Find.search RPRef.Find.search; rfl))
