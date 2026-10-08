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
  let __rp_tmp_a6beb2fc : Option (Nat × Nat) :=
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
  __rp_tmp_a6beb2fc
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (nums : List Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) :
    RPOrig.twoSum nums target h_precond = RPRef.twoSum nums target h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (nums : List Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) :
    RPOrig.twoSum nums target h_precond = RPRef.twoSum nums target h_precond := rfl

theorem rp_equiv_delta_rfl (nums : List Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) :
    RPOrig.twoSum nums target h_precond = RPRef.twoSum nums target h_precond := by
  delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.inner RPRef.twoSum.outer RPRef.twoSum.inner
  rfl

theorem rp_equiv_simp_only (nums : List Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) :
    RPOrig.twoSum nums target h_precond = RPRef.twoSum nums target h_precond := by
  (simp only [RPOrig.twoSum, RPRef.twoSum]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.inner RPRef.twoSum.outer RPRef.twoSum.inner; rfl))

theorem rp_equiv_simp (nums : List Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) :
    RPOrig.twoSum nums target h_precond = RPRef.twoSum nums target h_precond := by
  (simp [RPOrig.twoSum, RPRef.twoSum]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.twoSum RPRef.twoSum RPOrig.twoSum.outer RPOrig.twoSum.inner RPRef.twoSum.outer RPRef.twoSum.inner; rfl))
