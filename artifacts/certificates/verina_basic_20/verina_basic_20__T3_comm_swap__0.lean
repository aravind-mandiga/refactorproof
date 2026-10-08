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

def uniqueProduct (arr : Array Int) (h_precond : uniqueProduct_precond (arr)) : Int :=
  let rec loop (i : Nat) (seen : Std.HashSet Int) (product : Int) : Int :=
    if i < arr.size then
      let x := arr[i]!
      if seen.contains x then
        loop (1 + i) seen product
      else
        loop (i + 1) (seen.insert x) (product * x)
    else
      product
  loop 0 Std.HashSet.empty 1
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (arr : Array Int) (h_precond : uniqueProduct_precond (arr)) :
    RPOrig.uniqueProduct arr h_precond = RPRef.uniqueProduct arr h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (arr : Array Int) (h_precond : uniqueProduct_precond (arr)) :
    RPOrig.uniqueProduct arr h_precond = RPRef.uniqueProduct arr h_precond := rfl

theorem rp_equiv_delta_rfl (arr : Array Int) (h_precond : uniqueProduct_precond (arr)) :
    RPOrig.uniqueProduct arr h_precond = RPRef.uniqueProduct arr h_precond := by
  delta RPOrig.uniqueProduct RPRef.uniqueProduct RPOrig.uniqueProduct.loop RPRef.uniqueProduct.loop
  rfl

theorem rp_equiv_simp_only (arr : Array Int) (h_precond : uniqueProduct_precond (arr)) :
    RPOrig.uniqueProduct arr h_precond = RPRef.uniqueProduct arr h_precond := by
  first
    | (simp only [RPOrig.uniqueProduct, RPRef.uniqueProduct, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.uniqueProduct RPRef.uniqueProduct RPOrig.uniqueProduct.loop RPRef.uniqueProduct.loop; rfl))
    | (simp only [RPOrig.uniqueProduct, RPRef.uniqueProduct, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.uniqueProduct RPRef.uniqueProduct RPOrig.uniqueProduct.loop RPRef.uniqueProduct.loop; rfl))
    | (simp only [RPOrig.uniqueProduct, RPRef.uniqueProduct, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.uniqueProduct RPRef.uniqueProduct RPOrig.uniqueProduct.loop RPRef.uniqueProduct.loop; rfl))
    | (simp only [RPOrig.uniqueProduct, RPRef.uniqueProduct]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.uniqueProduct RPRef.uniqueProduct RPOrig.uniqueProduct.loop RPRef.uniqueProduct.loop; rfl))

theorem rp_equiv_simp (arr : Array Int) (h_precond : uniqueProduct_precond (arr)) :
    RPOrig.uniqueProduct arr h_precond = RPRef.uniqueProduct arr h_precond := by
  first
    | (simp [RPOrig.uniqueProduct, RPRef.uniqueProduct, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.uniqueProduct RPRef.uniqueProduct RPOrig.uniqueProduct.loop RPRef.uniqueProduct.loop; rfl))
    | (simp [RPOrig.uniqueProduct, RPRef.uniqueProduct, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.uniqueProduct RPRef.uniqueProduct RPOrig.uniqueProduct.loop RPRef.uniqueProduct.loop; rfl))
    | (simp [RPOrig.uniqueProduct, RPRef.uniqueProduct, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.uniqueProduct RPRef.uniqueProduct RPOrig.uniqueProduct.loop RPRef.uniqueProduct.loop; rfl))
    | (simp [RPOrig.uniqueProduct, RPRef.uniqueProduct]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.uniqueProduct RPRef.uniqueProduct RPOrig.uniqueProduct.loop RPRef.uniqueProduct.loop; rfl))

theorem rp_equiv_ac_rfl (arr : Array Int) (h_precond : uniqueProduct_precond (arr)) :
    RPOrig.uniqueProduct arr h_precond = RPRef.uniqueProduct arr h_precond := by
  (try simp only [RPOrig.uniqueProduct, RPRef.uniqueProduct]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.uniqueProduct RPRef.uniqueProduct RPOrig.uniqueProduct.loop RPRef.uniqueProduct.loop; rfl))
