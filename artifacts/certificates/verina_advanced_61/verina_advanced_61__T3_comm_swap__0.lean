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
  if n = 0 then []
  else
    let pref := computepref nums  -- length = n + 1, where prefix[i] = product of nums[0 ... i-1]
    let suffix := computeSuffix nums  -- length = n + 1, where suffix[i] = product of nums[i ... n-1]
    -- For each index i (0 ≤ i < n): result[i] = prefix[i] * suffix[i+1]
    -- Use array-style indexing as get! is deprecated
    List.range n |>.map (fun i => suffix[i+1]! * pref[i]!)
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
    | (simp only [RPOrig.productExceptSelf, RPRef.productExceptSelf, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.productExceptSelf RPRef.productExceptSelf; rfl))
    | (simp only [RPOrig.productExceptSelf, RPRef.productExceptSelf, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.productExceptSelf RPRef.productExceptSelf; rfl))
    | (simp only [RPOrig.productExceptSelf, RPRef.productExceptSelf, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.productExceptSelf RPRef.productExceptSelf; rfl))
    | (simp only [RPOrig.productExceptSelf, RPRef.productExceptSelf]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.productExceptSelf RPRef.productExceptSelf; rfl))

theorem rp_equiv_simp (nums : List Int) (h_precond : productExceptSelf_precond (nums)) :
    RPOrig.productExceptSelf nums h_precond = RPRef.productExceptSelf nums h_precond := by
  first
    | (simp [RPOrig.productExceptSelf, RPRef.productExceptSelf, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.productExceptSelf RPRef.productExceptSelf; rfl))
    | (simp [RPOrig.productExceptSelf, RPRef.productExceptSelf, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.productExceptSelf RPRef.productExceptSelf; rfl))
    | (simp [RPOrig.productExceptSelf, RPRef.productExceptSelf, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.productExceptSelf RPRef.productExceptSelf; rfl))
    | (simp [RPOrig.productExceptSelf, RPRef.productExceptSelf]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.productExceptSelf RPRef.productExceptSelf; rfl))

theorem rp_equiv_ac_rfl (nums : List Int) (h_precond : productExceptSelf_precond (nums)) :
    RPOrig.productExceptSelf nums h_precond = RPRef.productExceptSelf nums h_precond := by
  (try simp only [RPOrig.productExceptSelf, RPRef.productExceptSelf]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.productExceptSelf RPRef.productExceptSelf; rfl))
