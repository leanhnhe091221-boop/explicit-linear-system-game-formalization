module

public import ThomGame.Pictures.RimNonfacialCount
public import ThomGame.Pictures.CircuitCoverEdges

/-!
# A rim port belongs to a genuine facial label cover

This predicate uses an actual simple circuit, its face orbit and its
covering property. Uniqueness of rim continuation makes it constant on
the marked ports of any labelled circuit through that port.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open RibbonConnectivity

variable {R S : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
  {u v : List S} (G : SolutionGroup.RowGraph A u v) (γ : Hypergraph.Cycle A.hypergraph)

def RimFacialCoverAt (x : G.Dart) : Prop :=
  ∃ C : G.SimpleCircuit,
    (∀ i : Fin C.length, Port.label G.jointLabel (C.dart i) ∈ Set.range γ.edge) ∧
    (∃ side, C.BoundsFaceOrbit side) ∧ C.IsLabelCover ∧ C.Marked x

variable {G γ} (hu : ∀ z ∈ u, z ∉ Set.range γ.edge) (hv : ∀ z ∈ v, z ∉ Set.range γ.edge)
  (C : G.SimpleCircuit)
  (hlabels : ∀ i : Fin C.length, Port.label G.jointLabel (C.dart i) ∈ Set.range γ.edge)

include hu hv hlabels in
theorem rimFacialCoverAt_of_marked {x y : G.Dart} (hx : C.Marked x) (hy : C.Marked y)
    (hgood : G.RimFacialCoverAt γ x) : G.RimFacialCoverAt γ y := by
  obtain ⟨D, hl, hf, hc, hm⟩ := hgood
  exact ⟨D, hl, hf, hc, (C.marked_iff_of_common_rim_port γ hu hv hlabels D hl x hx hm y).mp hy⟩

include hu hv hlabels in
theorem rimFacialCoverAt_iff_circuit
    (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
      2 * Nat.card (Component G.circuitStep G.pairing.perm))
    {x : G.Dart} (hx : C.Marked x) :
    G.RimFacialCoverAt γ x ↔ (∃ side, C.BoundsFaceOrbit side) ∧ C.IsLabelCover := by
  constructor
  · rintro ⟨D, hl, ⟨side, hf⟩, hc, hm⟩
    have he := C.marked_iff_of_common_rim_port γ hu hv hlabels D hl x hx hm
    refine ⟨C.exists_face_of_marked_iff D he hEuler side hf, ?_⟩
    apply C.isLabelCover_iff_marked_edges.mpr
    intro y hy
    exact D.isLabelCover_iff_marked_edges.mp hc y ((he y).mp hy)
  · rintro ⟨hf, hc⟩
    exact ⟨C, hlabels, hf, hc, hx⟩

end ThomGame.Pictures.PortGraph
