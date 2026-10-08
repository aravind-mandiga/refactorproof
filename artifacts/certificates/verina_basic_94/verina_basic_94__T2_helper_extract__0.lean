-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def iter_copy_precond (s : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def iter_copy (s : Array Int) (h_precond : iter_copy_precond (s)) : Array Int :=
  let rec loop (i : Nat) (acc : Array Int) : Array Int :=
    if i < s.size then
      match s[i]? with
      | some val => loop (i + 1) (acc.push val)
      | none => acc  -- This case shouldn't happen when i < s.size
    else
      acc
  loop 0 Array.empty
end RPOrig

namespace RPRef
private def iter_copy__rp_helper_508df483 (s : Array Int) (h_precond : iter_copy_precond (s)) : Array Int :=
  let rec loop (i : Nat) (acc : Array Int) : Array Int :=
    if i < s.size then
      match s[i]? with
      | some val => loop (i + 1) (acc.push val)
      | none => acc  -- This case shouldn't happen when i < s.size
    else
      acc
  loop 0 Array.empty

def iter_copy (s : Array Int) (h_precond : iter_copy_precond (s)) : Array Int :=
  iter_copy__rp_helper_508df483 s h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (s : Array Int) (h_precond : iter_copy_precond (s)) :
    RPOrig.iter_copy s h_precond = RPRef.iter_copy s h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (s : Array Int) (h_precond : iter_copy_precond (s)) :
    RPOrig.iter_copy s h_precond = RPRef.iter_copy s h_precond := rfl

theorem rp_equiv_delta_rfl (s : Array Int) (h_precond : iter_copy_precond (s)) :
    RPOrig.iter_copy s h_precond = RPRef.iter_copy s h_precond := by
  delta RPOrig.iter_copy RPRef.iter_copy RPRef.iter_copy__rp_helper_508df483 RPOrig.iter_copy.loop RPRef.iter_copy__rp_helper_508df483.loop
  rfl

theorem rp_equiv_simp_only (s : Array Int) (h_precond : iter_copy_precond (s)) :
    RPOrig.iter_copy s h_precond = RPRef.iter_copy s h_precond := by
  (simp only [RPOrig.iter_copy, RPRef.iter_copy, RPRef.iter_copy__rp_helper_508df483]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.iter_copy RPRef.iter_copy RPRef.iter_copy__rp_helper_508df483 RPOrig.iter_copy.loop RPRef.iter_copy__rp_helper_508df483.loop; rfl))

theorem rp_equiv_simp (s : Array Int) (h_precond : iter_copy_precond (s)) :
    RPOrig.iter_copy s h_precond = RPRef.iter_copy s h_precond := by
  (simp [RPOrig.iter_copy, RPRef.iter_copy, RPRef.iter_copy__rp_helper_508df483]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.iter_copy RPRef.iter_copy RPRef.iter_copy__rp_helper_508df483 RPOrig.iter_copy.loop RPRef.iter_copy__rp_helper_508df483.loop; rfl))
