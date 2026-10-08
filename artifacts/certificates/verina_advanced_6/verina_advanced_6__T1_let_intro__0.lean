-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux
def toLower (c : Char) : Char :=
  if 'A' ≤ c && c ≤ 'Z' then
    Char.ofNat (Char.toNat c + 32)
  else
    c

def normalize_str (s : String) : List Char :=
  s.data.map toLower
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def allVowels_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def allVowels (s : String) (h_precond : allVowels_precond (s)) : Bool :=
  let chars := normalize_str s
  let vowelSet := ['a', 'e', 'i', 'o', 'u']
  vowelSet.all (fun v => chars.contains v)
end RPOrig

namespace RPRef

def allVowels (s : String) (h_precond : allVowels_precond (s)) : Bool :=
  let __rp_tmp_a77f67f1 : Bool :=
    let chars := normalize_str s
    let vowelSet := ['a', 'e', 'i', 'o', 'u']
    vowelSet.all (fun v => chars.contains v)
  __rp_tmp_a77f67f1
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (s : String) (h_precond : allVowels_precond (s)) :
    RPOrig.allVowels s h_precond = RPRef.allVowels s h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (s : String) (h_precond : allVowels_precond (s)) :
    RPOrig.allVowels s h_precond = RPRef.allVowels s h_precond := rfl

theorem rp_equiv_delta_rfl (s : String) (h_precond : allVowels_precond (s)) :
    RPOrig.allVowels s h_precond = RPRef.allVowels s h_precond := by
  delta RPOrig.allVowels RPRef.allVowels
  rfl

theorem rp_equiv_simp_only (s : String) (h_precond : allVowels_precond (s)) :
    RPOrig.allVowels s h_precond = RPRef.allVowels s h_precond := by
  (simp only [RPOrig.allVowels, RPRef.allVowels]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.allVowels RPRef.allVowels; rfl))

theorem rp_equiv_simp (s : String) (h_precond : allVowels_precond (s)) :
    RPOrig.allVowels s h_precond = RPRef.allVowels s h_precond := by
  (simp [RPOrig.allVowels, RPRef.allVowels]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.allVowels RPRef.allVowels; rfl))
