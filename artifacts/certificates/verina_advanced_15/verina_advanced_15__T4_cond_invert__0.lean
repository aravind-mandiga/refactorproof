-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def increasingTriplet_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def increasingTriplet (nums : List Int) (h_precond : increasingTriplet_precond (nums)) : Bool :=
  if nums.length < 3 then
    false
  else
    let rec loop (xs : List Int) (first : Option Int) (second : Option Int) : Bool :=
    match xs with
    | [] => false
    | x :: rest =>
      match first with
      | none => loop rest (some x) none
      | some f =>
        if x ≤ f then loop rest (some x) second
        else match second with
        | none => loop rest first (some x)
        | some s =>
          if x ≤ s then loop rest first (some x)
          else true
  loop nums none none
end RPOrig

namespace RPRef

def increasingTriplet (nums : List Int) (h_precond : increasingTriplet_precond (nums)) : Bool :=
  if ¬ (nums.length < 3) then
    let rec loop (xs : List Int) (first : Option Int) (second : Option Int) : Bool :=
    match xs with
    | [] => false
    | x :: rest =>
      match first with
      | none => loop rest (some x) none
      | some f =>
        if x ≤ f then loop rest (some x) second
        else match second with
        | none => loop rest first (some x)
        | some s =>
          if x ≤ s then loop rest first (some x)
          else true
  loop nums none none
  else
    false
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (nums : List Int) (h_precond : increasingTriplet_precond (nums)) :
    RPOrig.increasingTriplet nums h_precond = RPRef.increasingTriplet nums h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (nums : List Int) (h_precond : increasingTriplet_precond (nums)) :
    RPOrig.increasingTriplet nums h_precond = RPRef.increasingTriplet nums h_precond := rfl

theorem rp_equiv_delta_rfl (nums : List Int) (h_precond : increasingTriplet_precond (nums)) :
    RPOrig.increasingTriplet nums h_precond = RPRef.increasingTriplet nums h_precond := by
  delta RPOrig.increasingTriplet RPRef.increasingTriplet RPOrig.increasingTriplet.loop RPRef.increasingTriplet.loop
  rfl

theorem rp_equiv_simp_only (nums : List Int) (h_precond : increasingTriplet_precond (nums)) :
    RPOrig.increasingTriplet nums h_precond = RPRef.increasingTriplet nums h_precond := by
  first
    | (simp only [RPOrig.increasingTriplet, RPRef.increasingTriplet, ite_not]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.increasingTriplet RPRef.increasingTriplet RPOrig.increasingTriplet.loop RPRef.increasingTriplet.loop; rfl))
    | (simp only [RPOrig.increasingTriplet, RPRef.increasingTriplet, ite_not, Bool.not_eq_true, decide_not, Nat.not_lt, Nat.not_le, Int.not_lt, Int.not_le]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.increasingTriplet RPRef.increasingTriplet RPOrig.increasingTriplet.loop RPRef.increasingTriplet.loop; rfl))
    | (simp only [RPOrig.increasingTriplet, RPRef.increasingTriplet]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.increasingTriplet RPRef.increasingTriplet RPOrig.increasingTriplet.loop RPRef.increasingTriplet.loop; rfl))

theorem rp_equiv_simp (nums : List Int) (h_precond : increasingTriplet_precond (nums)) :
    RPOrig.increasingTriplet nums h_precond = RPRef.increasingTriplet nums h_precond := by
  first
    | (simp [RPOrig.increasingTriplet, RPRef.increasingTriplet, ite_not]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.increasingTriplet RPRef.increasingTriplet RPOrig.increasingTriplet.loop RPRef.increasingTriplet.loop; rfl))
    | (simp [RPOrig.increasingTriplet, RPRef.increasingTriplet, ite_not, Bool.not_eq_true, decide_not, Nat.not_lt, Nat.not_le, Int.not_lt, Int.not_le]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.increasingTriplet RPRef.increasingTriplet RPOrig.increasingTriplet.loop RPRef.increasingTriplet.loop; rfl))
    | (simp [RPOrig.increasingTriplet, RPRef.increasingTriplet]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.increasingTriplet RPRef.increasingTriplet RPOrig.increasingTriplet.loop RPRef.increasingTriplet.loop; rfl))

theorem rp_equiv_bycases (nums : List Int) (h_precond : increasingTriplet_precond (nums)) :
    RPOrig.increasingTriplet nums h_precond = RPRef.increasingTriplet nums h_precond := by
  by_cases h : (nums.length < 3) <;> (try simp [h, RPOrig.increasingTriplet, RPRef.increasingTriplet]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.increasingTriplet RPRef.increasingTriplet RPOrig.increasingTriplet.loop RPRef.increasingTriplet.loop; rfl))

theorem rp_equiv_bycases_ite (nums : List Int) (h_precond : increasingTriplet_precond (nums)) :
    RPOrig.increasingTriplet nums h_precond = RPRef.increasingTriplet nums h_precond := by
  by_cases h : (nums.length < 3) <;> (try simp [h, ite_not, RPOrig.increasingTriplet, RPRef.increasingTriplet]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.increasingTriplet RPRef.increasingTriplet RPOrig.increasingTriplet.loop RPRef.increasingTriplet.loop; rfl))

theorem rp_equiv_split_simp_all (nums : List Int) (h_precond : increasingTriplet_precond (nums)) :
    RPOrig.increasingTriplet nums h_precond = RPRef.increasingTriplet nums h_precond := by
  simp only [RPOrig.increasingTriplet, RPRef.increasingTriplet]; split <;> (try simp_all) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.increasingTriplet RPRef.increasingTriplet RPOrig.increasingTriplet.loop RPRef.increasingTriplet.loop; rfl))
