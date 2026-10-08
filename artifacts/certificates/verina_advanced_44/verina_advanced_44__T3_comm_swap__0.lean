-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def maxSubarraySumDivisibleByK_precond (arr : Array Int) (k : Int) : Prop :=
  -- !benchmark @start precond
  k > 0
  -- !benchmark @end precond



namespace RPOrig

def maxSubarraySumDivisibleByK (arr : Array Int) (k : Int) : Int :=
  let n := arr.size
  if n = 0 || k = 0 then 0
  else
    --compute prefix sums for efficient subarray sum calculation
    let prefixSums := Id.run do
      let mut prefixSums := Array.mkArray (n + 1) 0
      for i in [0:n] do
        prefixSums := prefixSums.set! (i+1) (prefixSums[i]! + arr[i]!)
      prefixSums

    let result := Id.run do
      let mut best : Option Int := none
      for len in List.range (n+1) do
        if len % k = 0 && len > 0 then
          for start in [0:(n - len + 1)] do
            let endIdx := start + len
            let subarraySum := prefixSums[endIdx]! - prefixSums[start]!
            best := match best with
              | none => some subarraySum
              | some b => some (max b subarraySum)
      best

    match result with
    | none => 0
    | some s => s
end RPOrig

namespace RPRef

def maxSubarraySumDivisibleByK (arr : Array Int) (k : Int) : Int :=
  let n := arr.size
  if n = 0 || k = 0 then 0
  else
    --compute prefix sums for efficient subarray sum calculation
    let prefixSums := Id.run do
      let mut prefixSums := Array.mkArray (1 + n) 0
      for i in [0:n] do
        prefixSums := prefixSums.set! (i+1) (prefixSums[i]! + arr[i]!)
      prefixSums

    let result := Id.run do
      let mut best : Option Int := none
      for len in List.range (n+1) do
        if len % k = 0 && len > 0 then
          for start in [0:(n - len + 1)] do
            let endIdx := start + len
            let subarraySum := prefixSums[endIdx]! - prefixSums[start]!
            best := match best with
              | none => some subarraySum
              | some b => some (max b subarraySum)
      best

    match result with
    | none => 0
    | some s => s
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (arr : Array Int) (k : Int) :
    RPOrig.maxSubarraySumDivisibleByK arr k = RPRef.maxSubarraySumDivisibleByK arr k := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (arr : Array Int) (k : Int) :
    RPOrig.maxSubarraySumDivisibleByK arr k = RPRef.maxSubarraySumDivisibleByK arr k := rfl

theorem rp_equiv_delta_rfl (arr : Array Int) (k : Int) :
    RPOrig.maxSubarraySumDivisibleByK arr k = RPRef.maxSubarraySumDivisibleByK arr k := by
  delta RPOrig.maxSubarraySumDivisibleByK RPRef.maxSubarraySumDivisibleByK
  rfl

theorem rp_equiv_simp_only (arr : Array Int) (k : Int) :
    RPOrig.maxSubarraySumDivisibleByK arr k = RPRef.maxSubarraySumDivisibleByK arr k := by
  first
    | (simp only [RPOrig.maxSubarraySumDivisibleByK, RPRef.maxSubarraySumDivisibleByK, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxSubarraySumDivisibleByK RPRef.maxSubarraySumDivisibleByK; rfl))
    | (simp only [RPOrig.maxSubarraySumDivisibleByK, RPRef.maxSubarraySumDivisibleByK, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxSubarraySumDivisibleByK RPRef.maxSubarraySumDivisibleByK; rfl))
    | (simp only [RPOrig.maxSubarraySumDivisibleByK, RPRef.maxSubarraySumDivisibleByK, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxSubarraySumDivisibleByK RPRef.maxSubarraySumDivisibleByK; rfl))
    | (simp only [RPOrig.maxSubarraySumDivisibleByK, RPRef.maxSubarraySumDivisibleByK]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxSubarraySumDivisibleByK RPRef.maxSubarraySumDivisibleByK; rfl))

theorem rp_equiv_simp (arr : Array Int) (k : Int) :
    RPOrig.maxSubarraySumDivisibleByK arr k = RPRef.maxSubarraySumDivisibleByK arr k := by
  first
    | (simp [RPOrig.maxSubarraySumDivisibleByK, RPRef.maxSubarraySumDivisibleByK, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxSubarraySumDivisibleByK RPRef.maxSubarraySumDivisibleByK; rfl))
    | (simp [RPOrig.maxSubarraySumDivisibleByK, RPRef.maxSubarraySumDivisibleByK, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxSubarraySumDivisibleByK RPRef.maxSubarraySumDivisibleByK; rfl))
    | (simp [RPOrig.maxSubarraySumDivisibleByK, RPRef.maxSubarraySumDivisibleByK, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxSubarraySumDivisibleByK RPRef.maxSubarraySumDivisibleByK; rfl))
    | (simp [RPOrig.maxSubarraySumDivisibleByK, RPRef.maxSubarraySumDivisibleByK]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxSubarraySumDivisibleByK RPRef.maxSubarraySumDivisibleByK; rfl))

theorem rp_equiv_ac_rfl (arr : Array Int) (k : Int) :
    RPOrig.maxSubarraySumDivisibleByK arr k = RPRef.maxSubarraySumDivisibleByK arr k := by
  (try simp only [RPOrig.maxSubarraySumDivisibleByK, RPRef.maxSubarraySumDivisibleByK]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxSubarraySumDivisibleByK RPRef.maxSubarraySumDivisibleByK; rfl))
