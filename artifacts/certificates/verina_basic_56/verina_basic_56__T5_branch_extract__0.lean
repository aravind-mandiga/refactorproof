-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def copy_precond (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) : Prop :=
  -- !benchmark @start precond
  src.size ≥ sStart + len ∧
  dest.size ≥ dStart + len
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def updateSegment : Array Int → Array Int → Nat → Nat → Nat → Array Int
  | r, src, sStart, dStart, 0 => r
  | r, src, sStart, dStart, n+1 =>
      let rNew := r.set! (dStart + n) (src[sStart + n]!)
      updateSegment rNew src sStart dStart n

namespace RPOrig

def copy (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) (h_precond : copy_precond (src) (sStart) (dest) (dStart) (len)) : Array Int :=
  if len = 0 then dest
  else
    let r := dest
    updateSegment r src sStart dStart len
end RPOrig

namespace RPRef

private def copy__rp_branch_559e9f9e (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) (h_precond : copy_precond (src) (sStart) (dest) (dStart) (len)) : Array Int :=
  let r := dest
  updateSegment r src sStart dStart len

def copy (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) (h_precond : copy_precond (src) (sStart) (dest) (dStart) (len)) : Array Int :=
  if len = 0 then dest
  else
    copy__rp_branch_559e9f9e src sStart dest dStart len h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) (h_precond : copy_precond (src) (sStart) (dest) (dStart) (len)) :
    RPOrig.copy src sStart dest dStart len h_precond = RPRef.copy src sStart dest dStart len h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) (h_precond : copy_precond (src) (sStart) (dest) (dStart) (len)) :
    RPOrig.copy src sStart dest dStart len h_precond = RPRef.copy src sStart dest dStart len h_precond := rfl

theorem rp_equiv_delta_rfl (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) (h_precond : copy_precond (src) (sStart) (dest) (dStart) (len)) :
    RPOrig.copy src sStart dest dStart len h_precond = RPRef.copy src sStart dest dStart len h_precond := by
  first
    | (delta RPOrig.copy RPRef.copy RPRef.copy__rp_branch_559e9f9e; rfl)
    | (delta RPOrig.copy RPRef.copy RPRef.copy__rp_branch_559e9f9e RPOrig.copy._unary; rfl)
    | (set_option smartUnfolding false in rfl)

theorem rp_equiv_simp_only (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) (h_precond : copy_precond (src) (sStart) (dest) (dStart) (len)) :
    RPOrig.copy src sStart dest dStart len h_precond = RPRef.copy src sStart dest dStart len h_precond := by
  (simp only [RPOrig.copy, RPRef.copy, RPRef.copy__rp_branch_559e9f9e]) <;> (first | rfl | (delta RPOrig.copy RPRef.copy RPRef.copy__rp_branch_559e9f9e; rfl) | (delta RPOrig.copy RPRef.copy RPRef.copy__rp_branch_559e9f9e RPOrig.copy._unary; rfl) | (set_option smartUnfolding false in rfl))

theorem rp_equiv_simp (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) (h_precond : copy_precond (src) (sStart) (dest) (dStart) (len)) :
    RPOrig.copy src sStart dest dStart len h_precond = RPRef.copy src sStart dest dStart len h_precond := by
  (simp [RPOrig.copy, RPRef.copy, RPRef.copy__rp_branch_559e9f9e]) <;> (first | rfl | (delta RPOrig.copy RPRef.copy RPRef.copy__rp_branch_559e9f9e; rfl) | (delta RPOrig.copy RPRef.copy RPRef.copy__rp_branch_559e9f9e RPOrig.copy._unary; rfl) | (set_option smartUnfolding false in rfl))
