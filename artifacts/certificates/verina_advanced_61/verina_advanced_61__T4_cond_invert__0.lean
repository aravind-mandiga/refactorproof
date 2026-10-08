-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def productExceptSelf_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
-- Helper: Compute prefix products.
-- prefix[i] is the product of all elements in nums before index i.
def computepref (nums : List Int) : List Int :=
  nums.foldl (fun acc x => acc ++ [acc.getLast! * x]) [1]

-- Helper: Compute suffix products.
-- suffix[i] is the product of all elements in nums from index i (inclusive) to the end.
-- We reverse the list and fold, then reverse back.
def computeSuffix (nums : List Int) : List Int :=
  let revSuffix := nums.reverse.foldl (fun acc x => acc ++ [acc.getLast! * x]) [1]
  revSuffix.reverse

namespace RPOrig

def productExceptSelf (nums : List Int) (h_precond : productExceptSelf_precond (nums)) : List Int :=
  let n := nums.length
  if n = 0 then []
  else
    let pref := computepref nums  -- length = n + 1, where prefix[i] = product of nums[0 ... i-1]
    let suffix := computeSuffix nums  -- length = n + 1, where suffix[i] = product of nums[i ... n-1]
    -- For each index i (0 ≤ i < n): result[i] = prefix[i] * suffix[i+1]
    -- Use array-style indexing as get! is deprecated
    List.range n |>.map (fun i => pref[i]! * suffix[i+1]!)
end RPOrig

namespace RPRef

def productExceptSelf (nums : List Int) (h_precond : productExceptSelf_precond (nums)) : List Int :=
  let n := nums.length
  if ¬ (n = 0) then
    let pref := computepref nums  -- length = n + 1, where prefix[i] = product of nums[0 ... i-1]
    let suffix := computeSuffix nums  -- length = n + 1, where suffix[i] = product of nums[i ... n-1]
    -- For each index i (0 ≤ i < n): result[i] = prefix[i] * suffix[i+1]
    -- Use array-style indexing as get! is deprecated
    List.range n |>.map (fun i => pref[i]! * suffix[i+1]!)
  else []
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (nums : List Int) (h_precond : productExceptSelf_precond (nums)) :
    RPOrig.productExceptSelf nums h_precond = RPRef.productExceptSelf nums h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (nums : List Int) (h_precond : productExceptSelf_precond (nums)) :
    RPOrig.productExceptSelf nums h_precond = RPRef.productExceptSelf nums h_precond := rfl

theorem rp_equiv_delta_rfl (nums : List Int) (h_precond : productExceptSelf_precond (nums)) :
    RPOrig.productExceptSelf nums h_precond = RPRef.productExceptSelf nums h_precond := by
  delta RPOrig.productExceptSelf RPRef.productExceptSelf
  rfl

theorem rp_equiv_simp_only (nums : List Int) (h_precond : productExceptSelf_precond (nums)) :
    RPOrig.productExceptSelf nums h_precond = RPRef.productExceptSelf nums h_precond := by
  first
    | (simp only [RPOrig.productExceptSelf, RPRef.productExceptSelf, ite_not]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.productExceptSelf RPRef.productExceptSelf; rfl))
    | (simp only [RPOrig.productExceptSelf, RPRef.productExceptSelf, ite_not, Bool.not_eq_true, decide_not, Nat.not_lt, Nat.not_le, Int.not_lt, Int.not_le]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.productExceptSelf RPRef.productExceptSelf; rfl))
    | (simp only [RPOrig.productExceptSelf, RPRef.productExceptSelf]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.productExceptSelf RPRef.productExceptSelf; rfl))

theorem rp_equiv_simp (nums : List Int) (h_precond : productExceptSelf_precond (nums)) :
    RPOrig.productExceptSelf nums h_precond = RPRef.productExceptSelf nums h_precond := by
  first
    | (simp [RPOrig.productExceptSelf, RPRef.productExceptSelf, ite_not]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.productExceptSelf RPRef.productExceptSelf; rfl))
    | (simp [RPOrig.productExceptSelf, RPRef.productExceptSelf, ite_not, Bool.not_eq_true, decide_not, Nat.not_lt, Nat.not_le, Int.not_lt, Int.not_le]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.productExceptSelf RPRef.productExceptSelf; rfl))
    | (simp [RPOrig.productExceptSelf, RPRef.productExceptSelf]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.productExceptSelf RPRef.productExceptSelf; rfl))

theorem rp_equiv_bycases (nums : List Int) (h_precond : productExceptSelf_precond (nums)) :
    RPOrig.productExceptSelf nums h_precond = RPRef.productExceptSelf nums h_precond := by
  by_cases h : (n = 0) <;> (try simp [h, RPOrig.productExceptSelf, RPRef.productExceptSelf]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.productExceptSelf RPRef.productExceptSelf; rfl))

theorem rp_equiv_bycases_ite (nums : List Int) (h_precond : productExceptSelf_precond (nums)) :
    RPOrig.productExceptSelf nums h_precond = RPRef.productExceptSelf nums h_precond := by
  by_cases h : (n = 0) <;> (try simp [h, ite_not, RPOrig.productExceptSelf, RPRef.productExceptSelf]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.productExceptSelf RPRef.productExceptSelf; rfl))

theorem rp_equiv_split_simp_all (nums : List Int) (h_precond : productExceptSelf_precond (nums)) :
    RPOrig.productExceptSelf nums h_precond = RPRef.productExceptSelf nums h_precond := by
  simp only [RPOrig.productExceptSelf, RPRef.productExceptSelf]; split <;> (try simp_all) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.productExceptSelf RPRef.productExceptSelf; rfl))
