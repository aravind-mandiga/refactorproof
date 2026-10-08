-- !benchmark @start import type=solution
import Std.Data.HashSet
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def uniqueProduct_precond (arr : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def uniqueProduct (arr : Array Int) (h_precond : uniqueProduct_precond (arr)) : Int :=
  let rec loop (i : Nat) (seen : Std.HashSet Int) (product : Int) : Int :=
    if i < arr.size then
      let x := arr[i]!
      if seen.contains x then
        loop (i + 1) seen product
      else
        loop (i + 1) (seen.insert x) (product * x)
    else
      product
  loop 0 Std.HashSet.empty 1
end RPOrig

namespace RPRef
private def uniqueProduct__rp_helper_cf50253c (arr : Array Int) (h_precond : uniqueProduct_precond (arr)) : Int :=
  let rec loop (i : Nat) (seen : Std.HashSet Int) (product : Int) : Int :=
    if i < arr.size then
      let x := arr[i]!
      if seen.contains x then
        loop (i + 1) seen product
      else
        loop (i + 1) (seen.insert x) (product * x)
    else
      product
  loop 0 Std.HashSet.empty 1

def uniqueProduct (arr : Array Int) (h_precond : uniqueProduct_precond (arr)) : Int :=
  uniqueProduct__rp_helper_cf50253c arr h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (arr : Array Int) (h_precond : uniqueProduct_precond (arr)) :
    RPOrig.uniqueProduct arr h_precond = RPRef.uniqueProduct arr h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (arr : Array Int) (h_precond : uniqueProduct_precond (arr)) :
    RPOrig.uniqueProduct arr h_precond = RPRef.uniqueProduct arr h_precond := rfl

theorem rp_equiv_delta_rfl (arr : Array Int) (h_precond : uniqueProduct_precond (arr)) :
    RPOrig.uniqueProduct arr h_precond = RPRef.uniqueProduct arr h_precond := by
  delta RPOrig.uniqueProduct RPRef.uniqueProduct RPRef.uniqueProduct__rp_helper_cf50253c RPOrig.uniqueProduct.loop RPRef.uniqueProduct__rp_helper_cf50253c.loop
  rfl

theorem rp_equiv_simp_only (arr : Array Int) (h_precond : uniqueProduct_precond (arr)) :
    RPOrig.uniqueProduct arr h_precond = RPRef.uniqueProduct arr h_precond := by
  (simp only [RPOrig.uniqueProduct, RPRef.uniqueProduct, RPRef.uniqueProduct__rp_helper_cf50253c]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.uniqueProduct RPRef.uniqueProduct RPRef.uniqueProduct__rp_helper_cf50253c RPOrig.uniqueProduct.loop RPRef.uniqueProduct__rp_helper_cf50253c.loop; rfl))

theorem rp_equiv_simp (arr : Array Int) (h_precond : uniqueProduct_precond (arr)) :
    RPOrig.uniqueProduct arr h_precond = RPRef.uniqueProduct arr h_precond := by
  (simp [RPOrig.uniqueProduct, RPRef.uniqueProduct, RPRef.uniqueProduct__rp_helper_cf50253c]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.uniqueProduct RPRef.uniqueProduct RPRef.uniqueProduct__rp_helper_cf50253c RPOrig.uniqueProduct.loop RPRef.uniqueProduct__rp_helper_cf50253c.loop; rfl))
