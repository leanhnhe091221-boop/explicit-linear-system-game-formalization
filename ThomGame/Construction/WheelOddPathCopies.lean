module

public import ThomGame.Construction.WheelOddCoveredPath
public import ThomGame.Pictures.RowPathComponents

/-!
# The covered part of the exceptional pentagon consists of three-edge copies

The path has the actual pentagon vertices 1, 2, 3, 4 and edges 2, 3, 4.
The general lifting equivalence describes all its actual hub occurrences,
preserves exactly the selected-edge adjacency, and gives four vertices in
each component. A copy that meets a chosen exceptional rim remains wholly
on that rim, where all its external ports face the same side.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures PortGraph

def oddPathVertexIndex : Fin 4 ↪ Fin 5 where
  toFun i := ⟨1 + i.val, by omega⟩
  inj' i j he := Fin.ext (by have hh := congrArg Fin.val he; dsimp at hh; omega)

def oddPathEdgeIndex : Fin 3 ↪ Fin 5 where
  toFun i := ⟨1 + i.val + 1, by omega⟩
  inj' i j he := Fin.ext (by have hh := congrArg Fin.val he; dsimp at hh; omega)

def oddCoveredRowPath : RowPath numberedSystem :=
  RowPath.ofCycleSegment (numberedWheelCycles oddWheelCycle) 1 3 (by decide +kernel)

theorem oddCoveredRowPath_edges : Set.range oddCoveredRowPath.edge = oddWheelCoveredEdges := by
  ext e
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨oddPathEdgeIndex i, by change 2 ≤ 1 + i.val + 1; omega, rfl⟩
  · rintro ⟨k, hk, he⟩
    have hklt : k.val < 5 := k.isLt
    let i : Fin 3 := ⟨k.val - 2, by omega⟩
    have hi : oddPathEdgeIndex i = k := Fin.ext (by change 1 + (k.val - 2) + 1 = k.val; omega)
    exact ⟨i, (congrArg (numberedWheelCycles oddWheelCycle).edge hi).trans he⟩

variable {H : SigmaGraph [] []}
  (hf : ∀ i : WheelCycleIndex, i ≠ oddWheelCycle → SigmaRimsFacialCovers H i)

include hf in
theorem oddCoveredRowPath_cover (x : H.Dart)
    (hx : Port.label H.jointLabel x ∈ Set.range oddCoveredRowPath.edge) : H.EdgeHasDistinctHubLabels x :=
  odd_covered_edge_distinct_labels hf x (oddCoveredRowPath_edges ▸ hx)

variable [IsEmpty H.Joint]

noncomputable def oddPathHubEquiv :
    H.LabelHub (oddCoveredRowPath.vertex 0) × Fin 4 ≃ oddCoveredRowPath.Node H :=
  oddCoveredRowPath.hubEquiv H (oddCoveredRowPath_cover hf)

include hf in
theorem oddPath_connected_iff (v w : oddCoveredRowPath.Node H) :
    oddCoveredRowPath.Connected H v w ↔ ((oddPathHubEquiv hf).symm v).1 = ((oddPathHubEquiv hf).symm w).1 :=
  oddCoveredRowPath.connected_iff_seed H (oddCoveredRowPath_cover hf) v w

include hf in
theorem oddPath_component_card (h : H.LabelHub (oddCoveredRowPath.vertex 0)) :
    Nat.card {v : oddCoveredRowPath.Node H //
      oddCoveredRowPath.Connected H (oddPathHubEquiv hf (h, 0)) v} = 4 :=
  oddCoveredRowPath.component_card H (oddCoveredRowPath_cover hf) h

variable (a : H.RimDart (numberedWheelCycles oddWheelCycle))
  (h : H.LabelHub (oddCoveredRowPath.vertex 0))
  (hh : (closedSigmaRimCircuit H oddWheelCycle a).OnCircuitVertex (.inr (.inl h.val)))

include hh in
theorem oddPath_hubs_on_rim (i : Fin 4) :
    (closedSigmaRimCircuit H oddWheelCycle a).OnCircuitVertex
      (.inr (.inl (oddCoveredRowPath.hub H (oddCoveredRowPath_cover hf) h i))) := by
  induction i using Fin.induction with
  | zero => exact hh
  | succ j ih =>
    obtain ⟨x, hx, hy, he⟩ := oddCoveredRowPath.lift_edge H (oddCoveredRowPath_cover hf) h j
    have hm := H.rimSimpleCircuit_marked_of_vertex_label (numberedWheelCycles oddWheelCycle) a
      (hx.symm ▸ ih) (oddWheelCoveredEdges_subset (oddCoveredRowPath_edges ▸ ⟨j, he.symm⟩))
    exact hy ▸ (closedSigmaRimCircuit H oddWheelCycle a).marked_onCircuitVertex
      (((closedSigmaRimCircuit H oddWheelCycle a).marked_twin_iff x).mpr hm)

noncomputable def oddPathRimVertex (i : Fin 4) :
    {v : H.Vertex // (closedSigmaRimCircuit H oddWheelCycle a).OnCircuitVertex v} :=
  ⟨.inr (.inl (oddCoveredRowPath.hub H (oddCoveredRowPath_cover hf) h i)),
    oddPath_hubs_on_rim hf a h hh i⟩

theorem oddPath_connected_in_rim (i : Fin 4) :
    (closedSigmaRimCircuit H oddWheelCycle a).RestrictedConnected oddWheelCoveredEdges
      (oddPathRimVertex hf a h hh 0) (oddPathRimVertex hf a h hh i) := by
  induction i using Fin.induction with
  | zero => exact Relation.EqvGen.refl _
  | succ j ih =>
    obtain ⟨x, hx, hy, he⟩ := oddCoveredRowPath.lift_edge H (oddCoveredRowPath_cover hf) h j
    have he' : Port.label H.jointLabel x ∈ oddWheelCoveredEdges := oddCoveredRowPath_edges ▸ ⟨j, he.symm⟩
    have hm := H.rimSimpleCircuit_marked_of_vertex_label (numberedWheelCycles oddWheelCycle) a
      (hx.symm ▸ oddPath_hubs_on_rim hf a h hh j.castSucc) (oddWheelCoveredEdges_subset he')
    exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ ⟨x, hm, he', hx, hy⟩)

include hh in
theorem oddPath_common_side : ∃ s, ∀ i : Fin 4, ∀ q : H.Dart,
    q.vertex = .inr (.inl (oddCoveredRowPath.hub H (oddCoveredRowPath_cover hf) h i)) →
    ¬ (closedSigmaRimCircuit H oddWheelCycle a).Marked q →
      (closedSigmaRimCircuit H oddWheelCycle a).Frontier s q := by
  obtain ⟨s, hs⟩ := odd_covered_component_common_side hf a (oddPathRimVertex hf a h hh 0)
  exact ⟨s, fun i q hq hn => hs (oddPathRimVertex hf a h hh i)
    (oddPath_connected_in_rim hf a h hh i) q hq hn⟩

end ThomGame.Construction
