-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start task_aux
structure Map (K V : Type) [BEq K] [BEq V] where
  entries : List (K × V)
deriving Inhabited

instance  (K V : Type) [BEq K] [BEq V] : BEq (Map K V) where
  beq m1 m2 := List.length m1.entries = List.length m2.entries ∧ List.beq m1.entries m2.entries

def empty {K V : Type} [BEq K] [BEq V] : Map K V := ⟨[]⟩

def insert {K V : Type} [BEq K] [BEq V] (m : Map K V) (k : K) (v : V) : Map K V :=
  let entries := m.entries.filter (fun p => ¬(p.1 == k)) ++ [(k, v)]
  ⟨entries⟩

-- !benchmark @end task_aux

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def update_map_precond (m1 : Map Int Int) (m2 : Map Int Int) : Prop :=
  -- !benchmark @start precond
  -- Both maps must have unique keys
  List.Nodup (m1.entries.map Prod.fst) ∧ List.Nodup (m2.entries.map Prod.fst)
  -- !benchmark @end precond



namespace RPOrig

def update_map (m1 : Map Int Int) (m2 : Map Int Int) (h_precond : update_map_precond (m1) (m2)) : Map Int Int :=
  let foldFn := fun (acc : Map Int Int) (entry : Int × Int) =>
    insert acc entry.1 entry.2
  let updated := m2.entries.foldl foldFn m1
  ⟨updated.entries.mergeSort (fun a b => a.1 ≤ b.1)⟩
end RPOrig

namespace RPRef
private def update_map__rp_helper_ca0c6cad (m1 : Map Int Int) (m2 : Map Int Int) (h_precond : update_map_precond (m1) (m2)) : Map Int Int :=
  let foldFn := fun (acc : Map Int Int) (entry : Int × Int) =>
    insert acc entry.1 entry.2
  let updated := m2.entries.foldl foldFn m1
  ⟨updated.entries.mergeSort (fun a b => a.1 ≤ b.1)⟩

def update_map (m1 : Map Int Int) (m2 : Map Int Int) (h_precond : update_map_precond (m1) (m2)) : Map Int Int :=
  update_map__rp_helper_ca0c6cad m1 m2 h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (m1 : Map Int Int) (m2 : Map Int Int) (h_precond : update_map_precond (m1) (m2)) :
    RPOrig.update_map m1 m2 h_precond = RPRef.update_map m1 m2 h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (m1 : Map Int Int) (m2 : Map Int Int) (h_precond : update_map_precond (m1) (m2)) :
    RPOrig.update_map m1 m2 h_precond = RPRef.update_map m1 m2 h_precond := rfl

theorem rp_equiv_delta_rfl (m1 : Map Int Int) (m2 : Map Int Int) (h_precond : update_map_precond (m1) (m2)) :
    RPOrig.update_map m1 m2 h_precond = RPRef.update_map m1 m2 h_precond := by
  delta RPOrig.update_map RPRef.update_map RPRef.update_map__rp_helper_ca0c6cad
  rfl

theorem rp_equiv_simp_only (m1 : Map Int Int) (m2 : Map Int Int) (h_precond : update_map_precond (m1) (m2)) :
    RPOrig.update_map m1 m2 h_precond = RPRef.update_map m1 m2 h_precond := by
  (simp only [RPOrig.update_map, RPRef.update_map, RPRef.update_map__rp_helper_ca0c6cad]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.update_map RPRef.update_map RPRef.update_map__rp_helper_ca0c6cad; rfl))

theorem rp_equiv_simp (m1 : Map Int Int) (m2 : Map Int Int) (h_precond : update_map_precond (m1) (m2)) :
    RPOrig.update_map m1 m2 h_precond = RPRef.update_map m1 m2 h_precond := by
  (simp [RPOrig.update_map, RPRef.update_map, RPRef.update_map__rp_helper_ca0c6cad]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.update_map RPRef.update_map RPRef.update_map__rp_helper_ca0c6cad; rfl))
