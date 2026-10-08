-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def reverseWords_precond (words_str : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def reverseWords (words_str : String) (h_precond : reverseWords_precond (words_str)) : String :=
  let rawWords : List String := words_str.splitOn " "
  let rec filterNonEmpty (words : List String) : List String :=
    match words with
    | [] => []
    | h :: t =>
      if h = "" then
        filterNonEmpty t
      else
        h :: filterNonEmpty t
  let filteredWords : List String := filterNonEmpty rawWords
  let revWords : List String := filteredWords.reverse
  let rec joinWithSpace (words : List String) : String :=
    match words with
    | [] => ""
    | [w] => w
    | h :: t =>
      -- Append the current word with a space and continue joining the rest.
      h ++ " " ++ joinWithSpace t
  let result : String := joinWithSpace revWords
  result
end RPOrig

namespace RPRef

def reverseWords (words_str : String) (h_precond : reverseWords_precond (words_str)) : String :=
  let __rp_tmp_fc0a1062 : String :=
    let rawWords : List String := words_str.splitOn " "
    let rec filterNonEmpty (words : List String) : List String :=
      match words with
      | [] => []
      | h :: t =>
        if h = "" then
          filterNonEmpty t
        else
          h :: filterNonEmpty t
    let filteredWords : List String := filterNonEmpty rawWords
    let revWords : List String := filteredWords.reverse
    let rec joinWithSpace (words : List String) : String :=
      match words with
      | [] => ""
      | [w] => w
      | h :: t =>
        -- Append the current word with a space and continue joining the rest.
        h ++ " " ++ joinWithSpace t
    let result : String := joinWithSpace revWords
    result
  __rp_tmp_fc0a1062
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (words_str : String) (h_precond : reverseWords_precond (words_str)) :
    RPOrig.reverseWords words_str h_precond = RPRef.reverseWords words_str h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (words_str : String) (h_precond : reverseWords_precond (words_str)) :
    RPOrig.reverseWords words_str h_precond = RPRef.reverseWords words_str h_precond := rfl

theorem rp_equiv_delta_rfl (words_str : String) (h_precond : reverseWords_precond (words_str)) :
    RPOrig.reverseWords words_str h_precond = RPRef.reverseWords words_str h_precond := by
  delta RPOrig.reverseWords RPRef.reverseWords RPOrig.reverseWords.filterNonEmpty RPOrig.reverseWords.joinWithSpace RPRef.reverseWords.filterNonEmpty RPRef.reverseWords.joinWithSpace
  rfl

theorem rp_equiv_simp_only (words_str : String) (h_precond : reverseWords_precond (words_str)) :
    RPOrig.reverseWords words_str h_precond = RPRef.reverseWords words_str h_precond := by
  (simp only [RPOrig.reverseWords, RPRef.reverseWords]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.reverseWords RPRef.reverseWords RPOrig.reverseWords.filterNonEmpty RPOrig.reverseWords.joinWithSpace RPRef.reverseWords.filterNonEmpty RPRef.reverseWords.joinWithSpace; rfl))

theorem rp_equiv_simp (words_str : String) (h_precond : reverseWords_precond (words_str)) :
    RPOrig.reverseWords words_str h_precond = RPRef.reverseWords words_str h_precond := by
  (simp [RPOrig.reverseWords, RPRef.reverseWords]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.reverseWords RPRef.reverseWords RPOrig.reverseWords.filterNonEmpty RPOrig.reverseWords.joinWithSpace RPRef.reverseWords.filterNonEmpty RPRef.reverseWords.joinWithSpace; rfl))
