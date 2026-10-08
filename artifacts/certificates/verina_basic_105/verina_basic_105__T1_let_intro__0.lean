-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def arrayProduct_precond (a : Array Int) (b : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size = b.size
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def loop (a b : Array Int) (len : Nat) : Nat → Array Int → Array Int
  | i, c =>
    if i < len then
      let a_val := if i < a.size then a[i]! else 0
      let b_val := if i < b.size then b[i]! else 0
      let new_c := Array.set! c i (a_val * b_val)
      loop a b len (i+1) new_c
    else c

namespace RPOrig

def arrayProduct (a : Array Int) (b : Array Int) (h_precond : arrayProduct_precond (a) (b)) : Array Int :=
  let len := a.size
  let c := Array.mkArray len 0
  loop a b len 0 c
end RPOrig

namespace RPRef

def arrayProduct (a : Array Int) (b : Array Int) (h_precond : arrayProduct_precond (a) (b)) : Array Int :=
  let __rp_tmp_f06d8879 : Array Int :=
    let len := a.size
    let c := Array.mkArray len 0
    loop a b len 0 c
  __rp_tmp_f06d8879
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (b : Array Int) (h_precond : arrayProduct_precond (a) (b)) :
    RPOrig.arrayProduct a b h_precond = RPRef.arrayProduct a b h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (b : Array Int) (h_precond : arrayProduct_precond (a) (b)) :
    RPOrig.arrayProduct a b h_precond = RPRef.arrayProduct a b h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (b : Array Int) (h_precond : arrayProduct_precond (a) (b)) :
    RPOrig.arrayProduct a b h_precond = RPRef.arrayProduct a b h_precond := by
  delta RPOrig.arrayProduct RPRef.arrayProduct
  rfl

theorem rp_equiv_simp_only (a : Array Int) (b : Array Int) (h_precond : arrayProduct_precond (a) (b)) :
    RPOrig.arrayProduct a b h_precond = RPRef.arrayProduct a b h_precond := by
  (simp only [RPOrig.arrayProduct, RPRef.arrayProduct]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.arrayProduct RPRef.arrayProduct; rfl))

theorem rp_equiv_simp (a : Array Int) (b : Array Int) (h_precond : arrayProduct_precond (a) (b)) :
    RPOrig.arrayProduct a b h_precond = RPRef.arrayProduct a b h_precond := by
  (simp [RPOrig.arrayProduct, RPRef.arrayProduct]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.arrayProduct RPRef.arrayProduct; rfl))
