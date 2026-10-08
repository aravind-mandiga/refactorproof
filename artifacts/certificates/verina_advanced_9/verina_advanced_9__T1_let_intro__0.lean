-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux
def sumOfDigits (x : Nat) : Nat :=
  let rec go (n acc : Nat) : Nat :=
    if n = 0 then acc
    else go (n / 10) (acc + (n % 10))
  go x 0
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def countSumDivisibleBy_precond (n : Nat) (d : Nat) : Prop :=
  -- !benchmark @start precond
  d > 0
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def isSumDivisibleBy (x : Nat) (d:Nat) : Bool :=
  (sumOfDigits x) % d = 0

namespace RPOrig

def countSumDivisibleBy (n : Nat) (d : Nat) (h_precond : countSumDivisibleBy_precond (n) (d)) : Nat :=
  let rec go (i acc : Nat) : Nat :=
    match i with
    | 0 => acc
    | i'+1 =>
      let acc' := if isSumDivisibleBy i' d then acc + 1 else acc
      go i' acc'
  go n 0
end RPOrig

namespace RPRef

def countSumDivisibleBy (n : Nat) (d : Nat) (h_precond : countSumDivisibleBy_precond (n) (d)) : Nat :=
  let __rp_tmp_ae05aafa : Nat :=
    let rec go (i acc : Nat) : Nat :=
      match i with
      | 0 => acc
      | i'+1 =>
        let acc' := if isSumDivisibleBy i' d then acc + 1 else acc
        go i' acc'
    go n 0
  __rp_tmp_ae05aafa
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (n : Nat) (d : Nat) (h_precond : countSumDivisibleBy_precond (n) (d)) :
    RPOrig.countSumDivisibleBy n d h_precond = RPRef.countSumDivisibleBy n d h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (n : Nat) (d : Nat) (h_precond : countSumDivisibleBy_precond (n) (d)) :
    RPOrig.countSumDivisibleBy n d h_precond = RPRef.countSumDivisibleBy n d h_precond := rfl

theorem rp_equiv_delta_rfl (n : Nat) (d : Nat) (h_precond : countSumDivisibleBy_precond (n) (d)) :
    RPOrig.countSumDivisibleBy n d h_precond = RPRef.countSumDivisibleBy n d h_precond := by
  delta RPOrig.countSumDivisibleBy RPRef.countSumDivisibleBy RPOrig.countSumDivisibleBy.go RPRef.countSumDivisibleBy.go
  rfl

theorem rp_equiv_simp_only (n : Nat) (d : Nat) (h_precond : countSumDivisibleBy_precond (n) (d)) :
    RPOrig.countSumDivisibleBy n d h_precond = RPRef.countSumDivisibleBy n d h_precond := by
  (simp only [RPOrig.countSumDivisibleBy, RPRef.countSumDivisibleBy]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.countSumDivisibleBy RPRef.countSumDivisibleBy RPOrig.countSumDivisibleBy.go RPRef.countSumDivisibleBy.go; rfl))

theorem rp_equiv_simp (n : Nat) (d : Nat) (h_precond : countSumDivisibleBy_precond (n) (d)) :
    RPOrig.countSumDivisibleBy n d h_precond = RPRef.countSumDivisibleBy n d h_precond := by
  (simp [RPOrig.countSumDivisibleBy, RPRef.countSumDivisibleBy]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.countSumDivisibleBy RPRef.countSumDivisibleBy RPOrig.countSumDivisibleBy.go RPRef.countSumDivisibleBy.go; rfl))
