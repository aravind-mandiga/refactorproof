-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def CanyonSearch_precond (a : Array Int) (b : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0 ∧ b.size > 0 ∧ List.Pairwise (· ≤ ·) a.toList ∧ List.Pairwise (· ≤ ·) b.toList
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def canyonSearchAux (a : Array Int) (b : Array Int) (m n d : Nat) : Nat :=
  if m < a.size ∧ n < b.size then
    let diff : Nat := ((a[m]! - b[n]!).natAbs)
    let new_d := if diff < d then diff else d
    if a[m]! <= b[n]! then
      canyonSearchAux a b (m + 1) n new_d
    else
      canyonSearchAux a b m (n + 1) new_d
  else
    d
termination_by a.size + b.size - m - n

namespace RPOrig

def CanyonSearch (a : Array Int) (b : Array Int) (h_precond : CanyonSearch_precond (a) (b)) : Nat :=
  let init : Nat :=
    if a[0]! < b[0]! then (b[0]! - a[0]!).natAbs
    else (a[0]! - b[0]!).natAbs
  canyonSearchAux a b 0 0 init
end RPOrig

namespace RPRef

def CanyonSearch (a : Array Int) (b : Array Int) (h_precond : CanyonSearch_precond (a) (b)) : Nat :=
  let __rp_tmp_767dd6b5 : Nat :=
    let init : Nat :=
      if a[0]! < b[0]! then (b[0]! - a[0]!).natAbs
      else (a[0]! - b[0]!).natAbs
    canyonSearchAux a b 0 0 init
  __rp_tmp_767dd6b5
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (b : Array Int) (h_precond : CanyonSearch_precond (a) (b)) :
    RPOrig.CanyonSearch a b h_precond = RPRef.CanyonSearch a b h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (b : Array Int) (h_precond : CanyonSearch_precond (a) (b)) :
    RPOrig.CanyonSearch a b h_precond = RPRef.CanyonSearch a b h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (b : Array Int) (h_precond : CanyonSearch_precond (a) (b)) :
    RPOrig.CanyonSearch a b h_precond = RPRef.CanyonSearch a b h_precond := by
  delta RPOrig.CanyonSearch RPRef.CanyonSearch
  rfl

theorem rp_equiv_simp_only (a : Array Int) (b : Array Int) (h_precond : CanyonSearch_precond (a) (b)) :
    RPOrig.CanyonSearch a b h_precond = RPRef.CanyonSearch a b h_precond := by
  (simp only [RPOrig.CanyonSearch, RPRef.CanyonSearch]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.CanyonSearch RPRef.CanyonSearch; rfl))

theorem rp_equiv_simp (a : Array Int) (b : Array Int) (h_precond : CanyonSearch_precond (a) (b)) :
    RPOrig.CanyonSearch a b h_precond = RPRef.CanyonSearch a b h_precond := by
  (simp [RPOrig.CanyonSearch, RPRef.CanyonSearch]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.CanyonSearch RPRef.CanyonSearch; rfl))
