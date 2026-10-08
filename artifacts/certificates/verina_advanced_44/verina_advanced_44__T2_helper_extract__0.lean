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
private def maxSubarraySumDivisibleByK__rp_helper_de6791bd (arr : Array Int) (k : Int) : Int :=
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

def maxSubarraySumDivisibleByK (arr : Array Int) (k : Int) : Int :=
  maxSubarraySumDivisibleByK__rp_helper_de6791bd arr k
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (arr : Array Int) (k : Int) :
    RPOrig.maxSubarraySumDivisibleByK arr k = RPRef.maxSubarraySumDivisibleByK arr k := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (arr : Array Int) (k : Int) :
    RPOrig.maxSubarraySumDivisibleByK arr k = RPRef.maxSubarraySumDivisibleByK arr k := rfl

theorem rp_equiv_delta_rfl (arr : Array Int) (k : Int) :
    RPOrig.maxSubarraySumDivisibleByK arr k = RPRef.maxSubarraySumDivisibleByK arr k := by
  delta RPOrig.maxSubarraySumDivisibleByK RPRef.maxSubarraySumDivisibleByK RPRef.maxSubarraySumDivisibleByK__rp_helper_de6791bd
  rfl

theorem rp_equiv_simp_only (arr : Array Int) (k : Int) :
    RPOrig.maxSubarraySumDivisibleByK arr k = RPRef.maxSubarraySumDivisibleByK arr k := by
  (simp only [RPOrig.maxSubarraySumDivisibleByK, RPRef.maxSubarraySumDivisibleByK, RPRef.maxSubarraySumDivisibleByK__rp_helper_de6791bd]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxSubarraySumDivisibleByK RPRef.maxSubarraySumDivisibleByK RPRef.maxSubarraySumDivisibleByK__rp_helper_de6791bd; rfl))

theorem rp_equiv_simp (arr : Array Int) (k : Int) :
    RPOrig.maxSubarraySumDivisibleByK arr k = RPRef.maxSubarraySumDivisibleByK arr k := by
  (simp [RPOrig.maxSubarraySumDivisibleByK, RPRef.maxSubarraySumDivisibleByK, RPRef.maxSubarraySumDivisibleByK__rp_helper_de6791bd]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxSubarraySumDivisibleByK RPRef.maxSubarraySumDivisibleByK RPRef.maxSubarraySumDivisibleByK__rp_helper_de6791bd; rfl))
