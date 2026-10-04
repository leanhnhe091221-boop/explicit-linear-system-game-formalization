module

public import ThomGame.Construction.WheelSunCovers
public import ThomGame.Pictures.RowGraphRimEmbedding

/-!
# Including the normalized sun graph into the actual numbered solution system

This is an operation on the sun port graph itself. Its complete port
equivalence retains pairing, rotation, and the prescribed boundary order.
The actual wheel retraction identifies all rim labels, so every canonical
rim circuit of the included Sigma graph is a facial cover whenever every
rim of the source sun graph is one. No diagram witness is substituted for
the normalized graph in this construction.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures
open scoped BigOperators

def numberedWheelSunEmbedding (i : WheelCycleIndex) :
    (Hypergraph.sunSystem (wheelCycles i).length (wheelCycles i).length_ge_three (fun _ => 0)).hypergraph.OpenEmbedding
      numberedSystem.hypergraph := (numberedWheelCycleRetraction i).inclusion

theorem numberedWheelSunEmbedding_vertex (i : WheelCycleIndex) (k : Fin (wheelCycles i).length) :
    (numberedWheelSunEmbedding i).vertex k = (numberedWheelCycleRetraction i).inclusion.vertex k := rfl

theorem numberedWheelSunEmbedding_rhs_zero (i : WheelCycleIndex) (hi : i ≠ oddWheelCycle)
    (k : Fin (wheelCycles i).length) :
    numberedSystem.rhs ((numberedWheelSunEmbedding i).vertex k) = 0 := by
  rw [numberedWheelSunEmbedding_vertex]
  exact numberedWheelCycleRetraction_rhs_zero i hi k

theorem numberedWheelSunEmbedding_rim (i : WheelCycleIndex)
    (x : Fin (wheelCycles i).length ⊕ Fin (wheelCycles i).length) :
    (numberedWheelSunEmbedding i).edge x ∈ Set.range (numberedWheelCycles i).edge ↔
      x ∈ Set.range (Hypergraph.sunCycle (wheelCycles i).length (wheelCycles i).length_ge_three).edge := by
  rw [← numberedWheelCycleRetraction_rim_range i]
  change (∃ j, (numberedWheelSunEmbedding i).edge (Sum.inr j) =
    (numberedWheelSunEmbedding i).edge x) ↔ ∃ j, Sum.inr j = x
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, (numberedWheelSunEmbedding i).edge.injective hj⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, congrArg (numberedWheelSunEmbedding i).edge hj⟩

variable (i : WheelCycleIndex) {u v : List (Fin (wheelCycles i).length ⊕ Fin (wheelCycles i).length)}
  (G : PortGraph (sunPresentation (wheelCycles i).length (fun _ => 0)) u v)

noncomputable def includeWheelSunGraph : SigmaGraph
    (u.map (numberedWheelSunEmbedding i).edge) (v.map (numberedWheelSunEmbedding i).edge) :=
  (G.sunRowGraph (wheelCycles i).length_ge_three).embedRows (numberedWheelSunEmbedding i)

noncomputable def includeWheelSunPorts : G.Dart ≃ (includeWheelSunGraph i G).Dart :=
  (G.sunRowGraph (wheelCycles i).length_ge_three).rowEmbeddingPorts (numberedWheelSunEmbedding i)

theorem includeWheelSunPorts_label (a : G.Dart) :
    Port.label (includeWheelSunGraph i G).jointLabel (includeWheelSunPorts i G a) =
      (numberedWheelSunEmbedding i).edge (Port.label G.jointLabel a) :=
  (G.sunRowGraph (wheelCycles i).length_ge_three).rowEmbeddingPorts_label (numberedWheelSunEmbedding i) a

theorem includeWheelSunPorts_twin (a : G.Dart) :
    (includeWheelSunGraph i G).pairing.twin (includeWheelSunPorts i G a) =
      includeWheelSunPorts i G (G.pairing.twin a) :=
  (G.sunRowGraph (wheelCycles i).length_ge_three).rowEmbeddingPorts_twin (numberedWheelSunEmbedding i) a

theorem includeWheelSunPorts_rotation (a : G.Dart) :
    (includeWheelSunGraph i G).rotation (includeWheelSunPorts i G a) =
      includeWheelSunPorts i G (G.rotation a) :=
  (G.sunRowGraph (wheelCycles i).length_ge_three).rowEmbeddingPorts_rotation (numberedWheelSunEmbedding i) a

theorem includeWheelSunGraph_hub_relations :
    (∑ h : (includeWheelSunGraph i G).Hub, ([(includeWheelSunGraph i G).hubLabel h] : Multiset (Fin 1417152))) =
      (∑ h : G.Hub, ([G.hubLabel h] : Multiset (Fin (wheelCycles i).length))).map
        (numberedWheelSunEmbedding i).vertex :=
  (G.sunRowGraph (wheelCycles i).length_ge_three).embedRows_hub_relations (numberedWheelSunEmbedding i)

theorem includeWheelSunGraph_hub_card : Fintype.card (includeWheelSunGraph i G).Hub = Fintype.card G.Hub := rfl

theorem includeWheelSunGraph_sign (hi : i ≠ oddWheelCycle) : (includeWheelSunGraph i G).sign = 0 :=
  (G.sunRowGraph (wheelCycles i).length_ge_three).embedRows_sign_zero (numberedWheelSunEmbedding i)
    (numberedWheelSunEmbedding_rhs_zero i hi)

theorem includeWheelSunGraph_noJoints [IsEmpty G.Joint] : IsEmpty (includeWheelSunGraph i G).Joint :=
  inferInstanceAs (IsEmpty G.Joint)

theorem includeWheelSunGraph_euler :
    Pictures.RibbonConnectivity.eulerDefect (includeWheelSunGraph i G).pairing.perm
      (includeWheelSunGraph i G).circuitStep =
        Pictures.RibbonConnectivity.eulerDefect G.pairing.perm G.circuitStep :=
  (G.sunRowGraph (wheelCycles i).length_ge_three).embedRows_eulerDefect (numberedWheelSunEmbedding i)

theorem includeWheelSunGraph_noncrossing (h : G.BoundaryNoncrossing) :
    (includeWheelSunGraph i G).BoundaryNoncrossing :=
  (G.sunRowGraph (wheelCycles i).length_ge_three).embedRows_boundaryNoncrossing (numberedWheelSunEmbedding i) h

theorem includeWheelSunGraph_sees (h : G.BoundarySeesComponents) :
    (includeWheelSunGraph i G).BoundarySeesComponents :=
  (G.sunRowGraph (wheelCycles i).length_ge_three).embedRows_boundarySeesComponents (numberedWheelSunEmbedding i) h

theorem includeWheelSunGraph_no_rim {w : List (Fin (wheelCycles i).length ⊕ Fin (wheelCycles i).length)}
    (hw : ∀ z ∈ w, ∃ j, z = Sum.inl j) :
    ∀ z ∈ w.map (numberedWheelSunEmbedding i).edge, z ∉ Set.range (numberedWheelCycles i).edge :=
  PortGraph.embeddedRim_no_boundary (numberedWheelSunEmbedding i)
    (Hypergraph.sunCycle (wheelCycles i).length (wheelCycles i).length_ge_three)
    (numberedWheelCycles i) (numberedWheelSunEmbedding_rim i)
    (sunBoundary_no_rim (wheelCycles i).length_ge_three hw)

variable {w : List (Fin (wheelCycles i).length ⊕ Fin (wheelCycles i).length)}
  (G : PortGraph (sunPresentation (wheelCycles i).length (fun _ => 0)) [] w)
  (hw : ∀ z ∈ w, ∃ j, z = Sum.inl j)

noncomputable def includedWheelSunRimCircuit
    (a : (includeWheelSunGraph i G).RimDart (numberedWheelCycles i)) :
    (includeWheelSunGraph i G).SimpleCircuit :=
  (includeWheelSunGraph i G).rimSimpleCircuit (numberedWheelCycles i) (by simp)
    (includeWheelSunGraph_no_rim i hw) a

theorem includedWheelSunRims_facial_covers
    (h : G.SunRimsFacialCovers (wheelCycles i).length_ge_three hw)
    (a : (includeWheelSunGraph i G).RimDart (numberedWheelCycles i)) :
    (∃ side, (includedWheelSunRimCircuit i G hw a).BoundsFaceOrbit side) ∧
      (includedWheelSunRimCircuit i G hw a).IsLabelCover := by
  let C := Hypergraph.sunCycle (wheelCycles i).length (wheelCycles i).length_ge_three
  let ι := numberedWheelSunEmbedding i
  let G₀ := G.sunRowGraph (wheelCycles i).length_ge_three
  let hu := sunBoundary_no_rim (wheelCycles i).length_ge_three (by simp : ∀ z ∈ ([] : List _), ∃ j, z = Sum.inl j)
  let hv := sunBoundary_no_rim (wheelCycles i).length_ge_three hw
  obtain ⟨a, rfl⟩ := (G₀.embeddedRimEquiv ι C (numberedWheelCycles i)
    (numberedWheelSunEmbedding_rim i)).surjective a
  obtain ⟨⟨side, hf⟩, hc⟩ := h a
  exact ⟨⟨side, G₀.embeddedRim_boundsFaceOrbit ι C (numberedWheelCycles i)
      (numberedWheelSunEmbedding_rim i) hu hv a side hf⟩,
    G₀.embeddedRim_isLabelCover ι C (numberedWheelCycles i)
      (numberedWheelSunEmbedding_rim i) hu hv a hc⟩

end ThomGame.Construction
