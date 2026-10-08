-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def twoSum_precond (nums : List Int) (target : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def twoSum (nums : List Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) : Option (Nat × Nat) :=
  let rec outer (lst : List Int) (i : Nat)
            : Option (Nat × Nat) :=
        match lst with
        | [] =>
            none
        | x :: xs =>
            let rec inner (lst' : List Int) (j : Nat)
                    : Option Nat :=
                match lst' with
                | [] =>
                    none
                | y :: ys =>
                    if x + y = target then
                        some j
                    else
                        inner ys (j + 1)
            match inner xs (i + 1) with
            | some j =>
                some (i, j)
            | none =>
                outer xs (i + 1)
        outer nums 0
end RPOrig

namespace RPRef

def twoSum (nums : List Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) : Option (Nat × Nat) :=
  let rec outer (lst : List Int) (i : Nat)
            : Option (Nat × Nat) :=
        match lst with
        | [] =>
            none
        | x :: xs =>
            let rec inner (lst' : List Int) (j : Nat)
                    : Option Nat :=
                match lst' with
                | [] =>
                    none
                | y :: ys =>
                    if y + x = target then
                        some j
                    else
                        inner ys (j + 1)
            match inner xs (i + 1) with
            | some j =>
                some (i, j)
            | none =>
                outer xs (i + 1)
        outer nums 0
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (nums : List Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) :
    RPOrig.twoSum nums target h_precond = RPRef.twoSum nums target h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (nums : List Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) :
    RPOrig.twoSum nums target h_precond = RPRef.twoSum nums target h_precond := rfl

theorem rp_equiv_delta_rfl (nums : List Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) :
    RPOrig.twoSum nums target h_precond = RPRef.twoSum nums target h_precond := by
  first
    | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner; rfl)
    | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner RPOrig.twoSum._unary RPOrig.twoSum.outer._unary RPOrig.twoSum.outer.inner._unary RPRef.twoSum.outer._unary RPRef.twoSum.outer.inner._unary; rfl)
    | (set_option smartUnfolding false in rfl)

theorem rp_equiv_simp_only (nums : List Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) :
    RPOrig.twoSum nums target h_precond = RPRef.twoSum nums target h_precond := by
  first
    | (simp only [RPOrig.twoSum, RPRef.twoSum, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner; rfl) | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner RPOrig.twoSum._unary RPOrig.twoSum.outer._unary RPOrig.twoSum.outer.inner._unary RPRef.twoSum.outer._unary RPRef.twoSum.outer.inner._unary; rfl) | (set_option smartUnfolding false in rfl))
    | (simp only [RPOrig.twoSum, RPRef.twoSum, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner; rfl) | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner RPOrig.twoSum._unary RPOrig.twoSum.outer._unary RPOrig.twoSum.outer.inner._unary RPRef.twoSum.outer._unary RPRef.twoSum.outer.inner._unary; rfl) | (set_option smartUnfolding false in rfl))
    | (simp only [RPOrig.twoSum, RPRef.twoSum, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner; rfl) | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner RPOrig.twoSum._unary RPOrig.twoSum.outer._unary RPOrig.twoSum.outer.inner._unary RPRef.twoSum.outer._unary RPRef.twoSum.outer.inner._unary; rfl) | (set_option smartUnfolding false in rfl))
    | (simp only [RPOrig.twoSum, RPRef.twoSum]) <;> (first | rfl | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner; rfl) | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner RPOrig.twoSum._unary RPOrig.twoSum.outer._unary RPOrig.twoSum.outer.inner._unary RPRef.twoSum.outer._unary RPRef.twoSum.outer.inner._unary; rfl) | (set_option smartUnfolding false in rfl))

theorem rp_equiv_simp (nums : List Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) :
    RPOrig.twoSum nums target h_precond = RPRef.twoSum nums target h_precond := by
  first
    | (simp [RPOrig.twoSum, RPRef.twoSum, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner; rfl) | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner RPOrig.twoSum._unary RPOrig.twoSum.outer._unary RPOrig.twoSum.outer.inner._unary RPRef.twoSum.outer._unary RPRef.twoSum.outer.inner._unary; rfl) | (set_option smartUnfolding false in rfl))
    | (simp [RPOrig.twoSum, RPRef.twoSum, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner; rfl) | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner RPOrig.twoSum._unary RPOrig.twoSum.outer._unary RPOrig.twoSum.outer.inner._unary RPRef.twoSum.outer._unary RPRef.twoSum.outer.inner._unary; rfl) | (set_option smartUnfolding false in rfl))
    | (simp [RPOrig.twoSum, RPRef.twoSum, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner; rfl) | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner RPOrig.twoSum._unary RPOrig.twoSum.outer._unary RPOrig.twoSum.outer.inner._unary RPRef.twoSum.outer._unary RPRef.twoSum.outer.inner._unary; rfl) | (set_option smartUnfolding false in rfl))
    | (simp [RPOrig.twoSum, RPRef.twoSum]) <;> (first | rfl | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner; rfl) | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner RPOrig.twoSum._unary RPOrig.twoSum.outer._unary RPOrig.twoSum.outer.inner._unary RPRef.twoSum.outer._unary RPRef.twoSum.outer.inner._unary; rfl) | (set_option smartUnfolding false in rfl))

theorem rp_equiv_ac_rfl (nums : List Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) :
    RPOrig.twoSum nums target h_precond = RPRef.twoSum nums target h_precond := by
  (try simp only [RPOrig.twoSum, RPRef.twoSum]) <;> (try ac_nf) <;> (first | rfl | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner; rfl) | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.outer.inner RPRef.twoSum.outer RPRef.twoSum.outer.inner RPOrig.twoSum._unary RPOrig.twoSum.outer._unary RPOrig.twoSum.outer.inner._unary RPRef.twoSum.outer._unary RPRef.twoSum.outer.inner._unary; rfl) | (set_option smartUnfolding false in rfl))
