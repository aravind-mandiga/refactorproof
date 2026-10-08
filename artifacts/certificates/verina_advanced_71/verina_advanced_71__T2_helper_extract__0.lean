-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux
def countOnes (lst : List Char) : Nat :=
  lst.foldl (fun acc c => if c = '1' then acc + 1 else acc) 0
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def shortestBeautifulSubstring_precond (s : String) (k : Nat) : Prop :=
  -- !benchmark @start precond
  s.toList.all (fun c => c = '0' ∨ c = '1')
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def listToString (lst : List Char) : String :=
  String.mk lst
def isLexSmaller (a b : List Char) : Bool :=
  listToString a < listToString b
def allSubstrings (s : List Char) : List (List Char) :=
  let n := s.length
  (List.range n).flatMap (fun i =>
    (List.range (n - i)).map (fun j =>
      s.drop i |>.take (j + 1)))

namespace RPOrig

def shortestBeautifulSubstring (s : String) (k : Nat) (h_precond : shortestBeautifulSubstring_precond (s) (k)) : String :=
  let chars := s.data
  let candidates := allSubstrings chars |>.filter (fun sub => countOnes sub = k)

  let compare (a b : List Char) : Bool :=
    a.length < b.length ∨ (a.length = b.length ∧ isLexSmaller a b)

  let best := candidates.foldl (fun acc cur =>
    match acc with
    | none => some cur
    | some best => if compare cur best then some cur else some best) none
  match best with
  | some b => listToString b
  | none => ""
end RPOrig

namespace RPRef

private def shortestBeautifulSubstring__rp_helper_7636fa4d (s : String) (k : Nat) (h_precond : shortestBeautifulSubstring_precond (s) (k)) : String :=
  let chars := s.data
  let candidates := allSubstrings chars |>.filter (fun sub => countOnes sub = k)

  let compare (a b : List Char) : Bool :=
    a.length < b.length ∨ (a.length = b.length ∧ isLexSmaller a b)

  let best := candidates.foldl (fun acc cur =>
    match acc with
    | none => some cur
    | some best => if compare cur best then some cur else some best) none
  match best with
  | some b => listToString b
  | none => ""

def shortestBeautifulSubstring (s : String) (k : Nat) (h_precond : shortestBeautifulSubstring_precond (s) (k)) : String :=
  shortestBeautifulSubstring__rp_helper_7636fa4d s k h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (s : String) (k : Nat) (h_precond : shortestBeautifulSubstring_precond (s) (k)) :
    RPOrig.shortestBeautifulSubstring s k h_precond = RPRef.shortestBeautifulSubstring s k h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (s : String) (k : Nat) (h_precond : shortestBeautifulSubstring_precond (s) (k)) :
    RPOrig.shortestBeautifulSubstring s k h_precond = RPRef.shortestBeautifulSubstring s k h_precond := rfl

theorem rp_equiv_delta_rfl (s : String) (k : Nat) (h_precond : shortestBeautifulSubstring_precond (s) (k)) :
    RPOrig.shortestBeautifulSubstring s k h_precond = RPRef.shortestBeautifulSubstring s k h_precond := by
  delta RPOrig.shortestBeautifulSubstring RPRef.shortestBeautifulSubstring RPRef.shortestBeautifulSubstring__rp_helper_7636fa4d
  rfl

theorem rp_equiv_simp_only (s : String) (k : Nat) (h_precond : shortestBeautifulSubstring_precond (s) (k)) :
    RPOrig.shortestBeautifulSubstring s k h_precond = RPRef.shortestBeautifulSubstring s k h_precond := by
  (simp only [RPOrig.shortestBeautifulSubstring, RPRef.shortestBeautifulSubstring, RPRef.shortestBeautifulSubstring__rp_helper_7636fa4d]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.shortestBeautifulSubstring RPRef.shortestBeautifulSubstring RPRef.shortestBeautifulSubstring__rp_helper_7636fa4d; rfl))

theorem rp_equiv_simp (s : String) (k : Nat) (h_precond : shortestBeautifulSubstring_precond (s) (k)) :
    RPOrig.shortestBeautifulSubstring s k h_precond = RPRef.shortestBeautifulSubstring s k h_precond := by
  (simp [RPOrig.shortestBeautifulSubstring, RPRef.shortestBeautifulSubstring, RPRef.shortestBeautifulSubstring__rp_helper_7636fa4d]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.shortestBeautifulSubstring RPRef.shortestBeautifulSubstring RPRef.shortestBeautifulSubstring__rp_helper_7636fa4d; rfl))
