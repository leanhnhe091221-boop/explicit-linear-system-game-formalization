module

public import ThomGame.Pictures.CycleCopyLift
public import ThomGame.Finite.CycleReindex
public import ThomGame.Finite.WheelCentralStellar
public import ThomGame.Finite.WheelPentagon

/-!
# Assembling the actual hubs and edges of a whole wheel

One central copy and the pentagon copies meeting its d edges determine
all three families of hubs. The c edges identify neighbouring pentagons,
so all four families of auxiliary edges have their required actual twins.
This construction applies before or after any row/column renumbering.
-/

@[expose] public section
namespace ThomGame.Wheel.Family

open Pictures PortGraph

variable {R V R' V' : Type*} [DecidableEq R] [DecidableEq V]
  [DecidableEq R'] [DecidableEq V'] (F : Family R V)
  (rows : F.Row ≃ R') (cols : F.Col ≃ V')
  (G : SolutionGroup.RowGraph (F.system.reindex rows cols) [] [])
  (r : R)

structure GraphLift where
  hub : Fin (F.size r) → Fin 3 → G.Hub
  label : ∀ j k, G.hubLabel (hub j k) = rows ⟨r, j, k⟩
  twin_a : ∀ j, G.pairing.twin (.hub (hub j 0) (1 : Fin 3)) =
    .hub (hub ((finRotate (F.size r)).symm j) (1 : Fin 3)) (2 : Fin 3)
  twin_b : ∀ j, G.pairing.twin (.hub (hub j 0) (2 : Fin 3)) = .hub (hub j 1) (0 : Fin 3)
  twin_c : ∀ j, G.pairing.twin (.hub (hub j 1) (1 : Fin 3)) = .hub (hub j 2) (0 : Fin 3)
  twin_d : ∀ j, G.pairing.twin (.hub (hub j 2) (1 : Fin 3)) =
    .hub (hub ((finRotate (F.size r)).symm j) (2 : Fin 3)) (2 : Fin 3)

variable (hlen : 3 ≤ F.size r)

abbrev reindexedCentralCycle := (F.centralCycle r hlen).reindexRows rows cols
abbrev reindexedPentagonCycle (j : Fin (F.size r)) := (F.pentagonCycle r j).reindexRows rows cols

variable {G}
  (B : G.CycleCopyLift (F.reindexedCentralCycle rows cols r hlen))
  (C : (j : Fin (F.size r)) → G.CycleCopyLift (F.reindexedPentagonCycle rows cols r j))
  (hC : ∀ j, (C j).hub 2 = B.hub j)

theorem central_lift_twin (j : Fin (F.size r)) :
    G.pairing.twin (.hub (B.hub j) (1 : Fin 3)) =
      .hub (B.hub ((finRotate (F.size r)).symm j)) (2 : Fin 3) := by
  apply B.twin j ((finRotate (F.size r)).symm j) 1 2 (Ne.symm (F.prev_ne_self r j))
  · refine ⟨j, ?_⟩
    change cols (F.aux r j 3) = (F.system.reindex rows cols).column (rows ⟨r, j, 2⟩) 1
    simp only [SparseSystem.reindex_column]
    simp [system, columns]
  · change (F.system.reindex rows cols).column (rows ⟨r, j, 2⟩) 1 =
      (F.system.reindex rows cols).column (rows ⟨r, (finRotate (F.size r)).symm j, 2⟩) 2
    simp only [SparseSystem.reindex_column]
    simp [system, columns]

theorem pentagon_copy_twins (j : Fin (F.size r))
    (P : G.CycleCopyLift (F.reindexedPentagonCycle rows cols r j)) :
    G.pairing.twin (.hub (P.hub 0) (1 : Fin 3)) = .hub (P.hub 4) (2 : Fin 3) ∧
    G.pairing.twin (.hub (P.hub 0) (2 : Fin 3)) = .hub (P.hub 1) (0 : Fin 3) ∧
    G.pairing.twin (.hub (P.hub 1) (1 : Fin 3)) = .hub (P.hub 2) (0 : Fin 3) ∧
    G.pairing.twin (.hub (P.hub 2) (1 : Fin 3)) = .hub (P.hub 3) (2 : Fin 3) ∧
    G.pairing.twin (.hub (P.hub 3) (0 : Fin 3)) = .hub (P.hub 4) (1 : Fin 3) := by
  have ht := P.twin
  refine ⟨ht 0 4 1 2 (by exact (by decide : (0 : Fin 5) ≠ 4)) ?_ ?_,
    ht 0 1 2 0 (by exact (by decide : (0 : Fin 5) ≠ 1)) ?_ ?_,
    ht 1 2 1 0 (by exact (by decide : (1 : Fin 5) ≠ 2)) ?_ ?_,
    ht 2 3 1 2 (by exact (by decide : (2 : Fin 5) ≠ 3)) ?_ ?_,
    ht 3 4 0 1 (by exact (by decide : (3 : Fin 5) ≠ 4)) ?_ ?_⟩
  · refine ⟨0, ?_⟩
    change cols (F.aux r (j) 0) =
      (F.system.reindex rows cols).column (rows ⟨r, j, 0⟩) 1
    simp only [SparseSystem.reindex_column]
    simp [system, columns]
  · change (F.system.reindex rows cols).column (rows ⟨r, j, 0⟩) 1 =
      (F.system.reindex rows cols).column (rows ⟨r, (finRotate (F.size r)).symm j, 1⟩) 2
    simp only [SparseSystem.reindex_column]
    simp [system, columns]
  · refine ⟨1, ?_⟩
    change cols (F.aux r (j) 1) =
      (F.system.reindex rows cols).column (rows ⟨r, j, 0⟩) 2
    simp only [SparseSystem.reindex_column]
    simp [system, columns]
  · change (F.system.reindex rows cols).column (rows ⟨r, j, 0⟩) 2 =
      (F.system.reindex rows cols).column (rows ⟨r, j, 1⟩) 0
    simp only [SparseSystem.reindex_column]
    simp [system, columns]
  · refine ⟨2, ?_⟩
    change cols (F.aux r (j) 2) =
      (F.system.reindex rows cols).column (rows ⟨r, j, 1⟩) 1
    simp only [SparseSystem.reindex_column]
    simp [system, columns]
  · change (F.system.reindex rows cols).column (rows ⟨r, j, 1⟩) 1 =
      (F.system.reindex rows cols).column (rows ⟨r, j, 2⟩) 0
    simp only [SparseSystem.reindex_column]
    simp [system, columns]
  · refine ⟨3, ?_⟩
    change cols (F.aux r (j) 3) =
      (F.system.reindex rows cols).column (rows ⟨r, j, 2⟩) 1
    simp only [SparseSystem.reindex_column]
    simp [system, columns]
  · change (F.system.reindex rows cols).column (rows ⟨r, j, 2⟩) 1 =
      (F.system.reindex rows cols).column (rows ⟨r, (finRotate (F.size r)).symm j, 2⟩) 2
    simp only [SparseSystem.reindex_column]
    simp [system, columns]
  · refine ⟨4, ?_⟩
    change cols (F.aux r ((finRotate (F.size r)).symm j) 2) =
      (F.system.reindex rows cols).column (rows ⟨r, (finRotate (F.size r)).symm j, 2⟩) 0
    simp only [SparseSystem.reindex_column]
    simp [system, columns]
  · change (F.system.reindex rows cols).column (rows ⟨r, (finRotate (F.size r)).symm j, 2⟩) 0 =
      (F.system.reindex rows cols).column (rows ⟨r, (finRotate (F.size r)).symm j, 1⟩) 1
    simp only [SparseSystem.reindex_column]
    simp [system, columns]

theorem pentagon_lift_twins (j : Fin (F.size r)) :
    G.pairing.twin (.hub ((C j).hub 0) (1 : Fin 3)) = .hub ((C j).hub 4) (2 : Fin 3) ∧
    G.pairing.twin (.hub ((C j).hub 0) (2 : Fin 3)) = .hub ((C j).hub 1) (0 : Fin 3) ∧
    G.pairing.twin (.hub ((C j).hub 1) (1 : Fin 3)) = .hub ((C j).hub 2) (0 : Fin 3) ∧
    G.pairing.twin (.hub ((C j).hub 2) (1 : Fin 3)) = .hub ((C j).hub 3) (2 : Fin 3) ∧
    G.pairing.twin (.hub ((C j).hub 3) (0 : Fin 3)) = .hub ((C j).hub 4) (1 : Fin 3) :=
  F.pentagon_copy_twins rows cols r j (C j)

include hC in
theorem pentagon_lift_central_prev (j : Fin (F.size r)) :
    (C j).hub 3 = B.hub ((finRotate (F.size r)).symm j) := by
  have hp := (F.pentagon_lift_twins rows cols r C j).2.2.2.1
  rw [hC j] at hp
  have he := hp.symm.trans (F.central_lift_twin rows cols r hlen B j)
  exact Sum.inl.inj (Sum.inr.inj (congrArg Port.vertex he))

include hC in
theorem pentagon_lift_neighbour (j : Fin (F.size r)) :
    (C j).hub 4 = (C ((finRotate (F.size r)).symm j)).hub 1 := by
  have hp := (F.pentagon_lift_twins rows cols r C j).2.2.2.2
  have hq := (F.pentagon_lift_twins rows cols r C ((finRotate (F.size r)).symm j)).2.2.1
  rw [F.pentagon_lift_central_prev rows cols r hlen B C hC j] at hp
  rw [hC] at hq
  have hi := (congrArg G.pairing.twin hq).symm.trans (G.pairing.involutive _)
  exact Sum.inl.inj (Sum.inr.inj (congrArg Port.vertex (hp.symm.trans hi)))

def assembledGraphLift : F.GraphLift rows cols G r where
  hub j := ![(C j).hub 0, (C j).hub 1, B.hub j]
  label j k := by
    fin_cases k
    · exact (C j).label 0
    · exact (C j).label 1
    · exact B.label j
  twin_a j := by
    change G.pairing.twin (.hub ((C j).hub 0) (1 : Fin 3)) = _
    rw [(F.pentagon_lift_twins rows cols r C j).1,
      F.pentagon_lift_neighbour rows cols r hlen B C hC j]
    rfl
  twin_b j := (F.pentagon_lift_twins rows cols r C j).2.1
  twin_c j := by
    change G.pairing.twin (.hub ((C j).hub 1) (1 : Fin 3)) = _
    rw [(F.pentagon_lift_twins rows cols r C j).2.2.1, hC j]
    rfl
  twin_d := F.central_lift_twin rows cols r hlen B

variable [IsEmpty G.Joint]

noncomputable def pentagonLiftAtCentral
    (hc : ∀ (j : Fin (F.size r)) (a : G.RimDart (F.reindexedPentagonCycle rows cols r j)),
      (G.rimSimpleCircuit _ (F.reindexedPentagonCycle rows cols r j).empty_boundary_no_rim
        (F.reindexedPentagonCycle rows cols r j).empty_boundary_no_rim a).IsLabelCopy)
    (j : Fin (F.size r)) : G.CycleCopyLift (F.reindexedPentagonCycle rows cols r j) := by
  let a : G.RimDart (F.reindexedPentagonCycle rows cols r j) :=
    ⟨.hub (B.hub j) (1 : Fin 3), ⟨3, by
      have hh : G.hubLabel (B.hub j) = rows ⟨r, j, 2⟩ := B.label j
      change cols (F.aux r j 3) =
        (F.system.reindex rows cols).column (G.hubLabel (B.hub j)) 1
      have he : cols (F.aux r j 3) = (F.system.reindex rows cols).column (rows ⟨r, j, 2⟩) 1 := by
        rw [SparseSystem.reindex_column]
        rfl
      exact he.trans (congrArg (fun x => (F.system.reindex rows cols).column x 1) hh).symm⟩⟩
  exact G.rimCopyLift _ a (hc j a)

theorem pentagonLiftAtCentral_seed
    (hc : ∀ (j : Fin (F.size r)) (a : G.RimDart (F.reindexedPentagonCycle rows cols r j)),
      (G.rimSimpleCircuit _ (F.reindexedPentagonCycle rows cols r j).empty_boundary_no_rim
        (F.reindexedPentagonCycle rows cols r j).empty_boundary_no_rim a).IsLabelCopy)
    (j : Fin (F.size r)) : (F.pentagonLiftAtCentral rows cols r hlen B hc j).hub 2 = B.hub j := by
  apply CycleCopyLift.hub_eq_of_label
  · exact G.rimCopyLift_seed _ _ _ (B.hub j) (1 : Fin 3) rfl
  · exact B.label j

noncomputable def graphLiftOfCentral
    (hc : ∀ (j : Fin (F.size r)) (a : G.RimDart (F.reindexedPentagonCycle rows cols r j)),
      (G.rimSimpleCircuit _ (F.reindexedPentagonCycle rows cols r j).empty_boundary_no_rim
        (F.reindexedPentagonCycle rows cols r j).empty_boundary_no_rim a).IsLabelCopy) :
    F.GraphLift rows cols G r :=
  F.assembledGraphLift rows cols r hlen B (F.pentagonLiftAtCentral rows cols r hlen B hc)
    (F.pentagonLiftAtCentral_seed rows cols r hlen B hc)

end ThomGame.Wheel.Family
