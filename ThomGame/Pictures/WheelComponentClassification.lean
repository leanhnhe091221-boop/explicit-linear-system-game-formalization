module

public import ThomGame.Pictures.WheelLiftComponents

/-!
# Every auxiliary component in a copied wheel picture is one whole wheel

Starting at any hub, its pentagon copy reaches a central hub. A central
copy through that hub and its adjacent pentagons give an actual wheel
lift. Its proved closure and connectivity identify the entire component.
-/

@[expose] public section
namespace ThomGame.Wheel.Family

open Pictures PortGraph Equiv
open scoped Classical BigOperators

variable {R V R' V' : Type*} [DecidableEq R] [DecidableEq V]
  [DecidableEq R'] [DecidableEq V'] (F : Family R V)
  (rows : F.Row ≃ R') (cols : F.Col ≃ V')
  (G : SolutionGroup.RowGraph (F.system.reindex rows cols) [] []) [IsEmpty G.Joint]
  (r : R) (hlen : 3 ≤ F.size r)
  (hb : ∀ a : G.RimDart (F.reindexedCentralCycle rows cols r hlen),
    (G.rimSimpleCircuit _ (F.reindexedCentralCycle rows cols r hlen).empty_boundary_no_rim
      (F.reindexedCentralCycle rows cols r hlen).empty_boundary_no_rim a).IsLabelCopy)
  (hp : ∀ (j : Fin (F.size r)) (a : G.RimDart (F.reindexedPentagonCycle rows cols r j)),
    (G.rimSimpleCircuit _ (F.reindexedPentagonCycle rows cols r j).empty_boundary_no_rim
      (F.reindexedPentagonCycle rows cols r j).empty_boundary_no_rim a).IsLabelCopy)

def WholeWheelComponent (h : G.Hub) : Prop :=
  ∃ L : F.GraphLift rows cols G r,
      (∀ x, F.AuxiliaryConnected rows cols G h x ↔ L.Contains x) ∧
      (∀ i l, ∃! x : G.Hub,
        F.AuxiliaryConnected rows cols G h x ∧ G.hubLabel x = rows ⟨r, i, l⟩) ∧
      Fintype.card {x : G.Hub // F.AuxiliaryConnected rows cols G h x} = 3 * F.size r ∧
      (∑ x : {x : G.Hub // F.AuxiliaryConnected rows cols G h x},
        (F.system.reindex rows cols).rhs (G.hubLabel x.val)) = F.parity r

include hb hp

theorem exists_graphLift_containing (h : G.Hub) (j : Fin (F.size r)) (k : Fin 3)
    (hh : G.hubLabel h = rows ⟨r, j, k⟩) :
    ∃ L : F.GraphLift rows cols G r, L.Contains h := by
  have hport (p : Fin 3) : Port.label G.jointLabel (.hub h p : G.Dart) =
      cols (F.columns r j k p) := by
    rw [SolutionGroup.rowGraph_port_label, hh, SparseSystem.reindex_column]
    rfl
  have hm : ∃ p : Fin 3, Port.label G.jointLabel (.hub h p : G.Dart) ∈
      Set.range (F.reindexedPentagonCycle rows cols r j).edge := by
    fin_cases k
    · exact ⟨1, ⟨0, (hport 1).symm⟩⟩
    · exact ⟨0, ⟨1, (hport 0).symm⟩⟩
    · exact ⟨1, ⟨3, (hport 1).symm⟩⟩
  obtain ⟨p, hpm⟩ := hm
  let a : G.RimDart (F.reindexedPentagonCycle rows cols r j) := ⟨.hub h p, hpm⟩
  let P := G.rimCopyLift _ a (hp j a)
  have hPr : h ∈ Set.range P.hub := G.rimCopyLift_seed _ a (hp j a) h p rfl
  have hP2 : G.hubLabel (P.hub 2) = rows ⟨r, j, 2⟩ := P.label 2
  have hBm : Port.label G.jointLabel (.hub (P.hub 2) (1 : Fin 3) : G.Dart) ∈
      Set.range (F.reindexedCentralCycle rows cols r hlen).edge := by
    refine ⟨j, ?_⟩
    change cols (F.aux r j 3) = _
    rw [SolutionGroup.rowGraph_port_label, hP2, SparseSystem.reindex_column]
    rfl
  let b : G.RimDart (F.reindexedCentralCycle rows cols r hlen) := ⟨.hub (P.hub 2) (1 : Fin 3), hBm⟩
  let B := G.rimCopyLift _ b (hb b)
  have hBj : B.hub j = P.hub 2 := B.hub_eq_of_label
    (G.rimCopyLift_seed _ b (hb b) (P.hub 2) 1 rfl) j hP2
  let L := F.graphLiftOfCentral rows cols r hlen B hp
  have hLc : L.Contains (P.hub 2) := ⟨j, 2, hBj⟩
  have htw := F.pentagon_copy_twins rows cols r j P
  have h01 : F.AuxiliaryConnected rows cols G (P.hub 0) (P.hub 1) := by
    refine Relation.EqvGen.rel _ _ ⟨2, 0, ⟨r, j, 1⟩, htw.2.1, ?_⟩
    have hl : G.hubLabel (P.hub 0) = rows ⟨r, j, 0⟩ := P.label 0
    rw [SolutionGroup.rowGraph_port_label, hl, SparseSystem.reindex_column]
    rfl
  have h12 : F.AuxiliaryConnected rows cols G (P.hub 1) (P.hub 2) := by
    refine Relation.EqvGen.rel _ _ ⟨1, 0, ⟨r, j, 2⟩, htw.2.2.1, ?_⟩
    have hl : G.hubLabel (P.hub 1) = rows ⟨r, j, 1⟩ := P.label 1
    rw [SolutionGroup.rowGraph_port_label, hl, SparseSystem.reindex_column]
    rfl
  refine ⟨L, ?_⟩
  fin_cases k
  · have he : P.hub 0 = h := P.hub_eq_of_label hPr 0 hh
    exact he ▸ (L.contains_iff_of_connected (Relation.EqvGen.trans _ _ _ h01 h12)).mpr hLc
  · have he : P.hub 1 = h := P.hub_eq_of_label hPr 1 hh
    exact he ▸ (L.contains_iff_of_connected h12).mpr hLc
  · have he : P.hub 2 = h := P.hub_eq_of_label hPr 2 hh
    exact he ▸ hLc

theorem component_one_hub_per_row (h : G.Hub) (j : Fin (F.size r)) (k : Fin 3)
    (hh : G.hubLabel h = rows ⟨r, j, k⟩) :
    F.WholeWheelComponent rows cols G r h := by
  obtain ⟨L, i, l, hi⟩ := F.exists_graphLift_containing rows cols G r hlen hb hp h j k hh
  subst h
  refine ⟨L, fun x => (L.contains_iff_connected i l x).symm, ?_,
    L.component_card i l, L.component_rhs_sum i l⟩
  intro j k
  simpa only [← L.contains_iff_connected i l] using L.unique_hub_over_row j k

omit hb hp in
theorem every_hub_in_whole_wheel
    (hlen : ∀ r, 3 ≤ F.size r)
    (hb : ∀ (r : R) (a : G.RimDart (F.reindexedCentralCycle rows cols r (hlen r))),
      (G.rimSimpleCircuit _ (F.reindexedCentralCycle rows cols r (hlen r)).empty_boundary_no_rim
        (F.reindexedCentralCycle rows cols r (hlen r)).empty_boundary_no_rim a).IsLabelCopy)
    (hp : ∀ (r : R) (j : Fin (F.size r)) (a : G.RimDart (F.reindexedPentagonCycle rows cols r j)),
      (G.rimSimpleCircuit _ (F.reindexedPentagonCycle rows cols r j).empty_boundary_no_rim
        (F.reindexedPentagonCycle rows cols r j).empty_boundary_no_rim a).IsLabelCopy)
    (h : G.Hub) :
    ∃ r : R, F.WholeWheelComponent rows cols G r h := by
  obtain ⟨⟨r, j, k⟩, hh⟩ := rows.surjective (G.hubLabel h)
  exact ⟨r, F.component_one_hub_per_row rows cols G r (hlen r) (hb r) (hp r) h j k hh.symm⟩

end ThomGame.Wheel.Family
