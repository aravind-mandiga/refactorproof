-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def swap_precond (arr : Array Int) (i : Int) (j : Int) : Prop :=
  -- !benchmark @start precond
  i ≥ 0 ∧
  j ≥ 0 ∧
  Int.toNat i < arr.size ∧
  Int.toNat j < arr.size
  -- !benchmark @end precond



namespace RPOrig

def swap (arr : Array Int) (i : Int) (j : Int) (h_precond : swap_precond (arr) (i) (j)) : Array Int :=
  let i_nat := Int.toNat i
  let j_nat := Int.toNat j
  let arr1 := arr.set! i_nat (arr[j_nat]!)
  let arr2 := arr1.set! j_nat (arr[i_nat]!)
  arr2
end RPOrig

namespace RPRef

def swap (arr : Array Int) (i : Int) (j : Int) (h_precond : swap_precond (arr) (i) (j)) : Array Int :=
  let __rp_tmp_11eb44d6 : Array Int :=
    let i_nat := Int.toNat i
    let j_nat := Int.toNat j
    let arr1 := arr.set! i_nat (arr[j_nat]!)
    let arr2 := arr1.set! j_nat (arr[i_nat]!)
    arr2
  __rp_tmp_11eb44d6
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (arr : Array Int) (i : Int) (j : Int) (h_precond : swap_precond (arr) (i) (j)) :
    RPOrig.swap arr i j h_precond = RPRef.swap arr i j h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (arr : Array Int) (i : Int) (j : Int) (h_precond : swap_precond (arr) (i) (j)) :
    RPOrig.swap arr i j h_precond = RPRef.swap arr i j h_precond := rfl

theorem rp_equiv_delta_rfl (arr : Array Int) (i : Int) (j : Int) (h_precond : swap_precond (arr) (i) (j)) :
    RPOrig.swap arr i j h_precond = RPRef.swap arr i j h_precond := by
  delta RPOrig.swap RPRef.swap
  rfl

theorem rp_equiv_simp_only (arr : Array Int) (i : Int) (j : Int) (h_precond : swap_precond (arr) (i) (j)) :
    RPOrig.swap arr i j h_precond = RPRef.swap arr i j h_precond := by
  (simp only [RPOrig.swap, RPRef.swap]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.swap RPRef.swap; rfl))

theorem rp_equiv_simp (arr : Array Int) (i : Int) (j : Int) (h_precond : swap_precond (arr) (i) (j)) :
    RPOrig.swap arr i j h_precond = RPRef.swap arr i j h_precond := by
  (simp [RPOrig.swap, RPRef.swap]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.swap RPRef.swap; rfl))
