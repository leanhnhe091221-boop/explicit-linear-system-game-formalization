module

public import ThomGame.Pictures.SunRimCover
public import ThomGame.Pictures.CycleSimpleCircuit

/-!
# Label covers at individual actual edges

Covering is independent of the chosen direction on a circuit edge.
Every dart whose label is on a covered hypergraph cycle therefore has
two differently labelled hub endpoints. In particular this property
passes to edges shared with another cycle.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  {G : PortGraph P u v}

def EdgeHasDistinctHubLabels (G : PortGraph P u v) (x : G.Dart) : Prop :=
  ∃ (h k : G.Hub)
    (p : Fin (P.word (G.hubLabel h)).length) (q : Fin (P.word (G.hubLabel k)).length),
    x = .hub h p ∧ G.pairing.twin x = .hub k q ∧ h ≠ k ∧ G.hubLabel h ≠ G.hubLabel k

theorem edgeHasDistinctHubLabels_twin_iff (x : G.Dart) :
    G.EdgeHasDistinctHubLabels (G.pairing.twin x) ↔ G.EdgeHasDistinctHubLabels x := by
  have ht (y : G.Dart) (h : G.EdgeHasDistinctHubLabels y) :
      G.EdgeHasDistinctHubLabels (G.pairing.twin y) := by
    obtain ⟨h, k, p, q, hp, hq, hk, hl⟩ := h
    exact ⟨k, h, q, p, hq, (G.pairing.involutive y).trans hp, hk.symm, hl.symm⟩
  exact ⟨fun h => G.pairing.involutive x ▸ ht _ h, ht x⟩

namespace SimpleCircuit

variable (C : G.SimpleCircuit)

theorem isLabelCover_iff_marked_edges : C.IsLabelCover ↔
    ∀ x : G.Dart, C.Marked x → G.EdgeHasDistinctHubLabels x := by
  constructor
  · intro h x hx
    obtain ⟨⟨i, side⟩, rfl⟩ := hx
    cases side
    · exact h i
    · exact (edgeHasDistinctHubLabels_twin_iff _).mpr (h ((finRotate C.length).symm i))
  · intro h i
    exact h _ ⟨(i, false), rfl⟩

end SimpleCircuit

variable {A : SparseSystem R S} [DecidableEq R] [DecidableEq S]
  {H : SolutionGroup.RowGraph A [] []} (D : Hypergraph.Cycle A.hypergraph)

theorem rim_cover_edge (hc : ∀ a : H.RimDart D,
    (H.rimSimpleCircuit D (by simp) (by simp) a).IsLabelCover)
    (x : H.Dart) (hx : Port.label H.jointLabel x ∈ Set.range D.edge) :
    H.EdgeHasDistinctHubLabels x := by
  let a : H.RimDart D := ⟨x, hx⟩
  have h := hc a 0
  have he : (H.rimSimpleCircuit D (by simp) (by simp) a).dart 0 = x :=
    congrArg Subtype.val (OrbitEnumeration.dart_zero (H.rimWalk D (by simp) (by simp)) a)
  change H.EdgeHasDistinctHubLabels ((H.rimSimpleCircuit D (by simp) (by simp) a).dart 0) at h
  exact he ▸ h

end ThomGame.Pictures.PortGraph
