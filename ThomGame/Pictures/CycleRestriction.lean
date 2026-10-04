module

public import ThomGame.Finite.CycleRows
public import ThomGame.Pictures.SolutionGraph

/-!
# Restriction of an actual row graph to a hypergraph cycle

Retain precisely the darts labelled by rim edges. Their original edge
pairing restricts, and if no rim edge occurs on the boundary, every
retained vertex has exactly two retained darts. These are the finite
incidence data underlying Slofstra Lemma 9.2, with subdivision vertices
included. A geometric simple-curve realization is not asserted here.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

variable {R S : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
  {u v : List S} (G : SolutionGroup.RowGraph A u v) (C : Hypergraph.Cycle A.hypergraph)

def RimDart := {a : G.Dart // Port.label G.jointLabel a ∈ Set.range C.edge}

noncomputable instance : Fintype (G.RimDart C) := by
  classical
  unfold RimDart
  infer_instance

def rimPairing : Pairing (fun a : G.RimDart C => Port.label G.jointLabel a.val) where
  twin a := ⟨G.pairing.twin a.val, by rw [G.pairing.label_twin]; exact a.property⟩
  involutive a := Subtype.ext (G.pairing.involutive a.val)
  ne_self a he := G.pairing.ne_self a.val (congrArg Subtype.val he)
  label_twin a := G.pairing.label_twin a.val

def rimEdgeToEdge : (G.rimPairing C).Edge → G.Edge :=
  Quotient.lift (fun a => G.pairing.edge a.val) (by
    intro a b hab
    apply (G.pairing.edge_eq_iff a.val b.val).mpr
    rcases hab with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h))

theorem rimEdgeToEdge_injective : Function.Injective (G.rimEdgeToEdge C) := by
  intro x y
  refine Quotient.inductionOn₂ x y (fun a b hab => ?_)
  change G.pairing.edge a.val = G.pairing.edge b.val at hab
  apply ((G.rimPairing C).edge_eq_iff a b).mpr
  rcases (G.pairing.edge_eq_iff a.val b.val).mp hab with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

def RimIncident (x : G.Vertex) := {a : G.RimDart C // a.val.vertex = x}

noncomputable instance (x : G.Vertex) : Fintype (G.RimIncident C x) := by
  classical
  unfold RimIncident
  infer_instance

noncomputable def rimIncidentEquiv (x : G.Vertex) :
    {i : Port.Slots (P := SolutionGroup.triangularPresentation A) (hubLabel := G.hubLabel) x //
      Port.label G.jointLabel (Port.atVertex x i) ∈ Set.range C.edge} ≃ G.RimIncident C x :=
  Equiv.ofBijective
    (fun i => ⟨⟨Port.atVertex x i.val, i.property⟩, Port.vertex_at x i.val⟩)
    (by
      constructor
      · intro i j hij
        apply Subtype.ext
        apply (Port.incidentEquiv (P := SolutionGroup.triangularPresentation A)
          (hubLabel := G.hubLabel) x).injective
        apply Subtype.ext
        exact congrArg (fun a : G.RimIncident C x => a.val.val) hij
      · intro a
        obtain ⟨i, hi⟩ := (Port.incidentEquiv (P := SolutionGroup.triangularPresentation A)
          (hubLabel := G.hubLabel) x).surjective ⟨a.val.val, a.property⟩
        have he : Port.atVertex x i = a.val.val := congrArg Subtype.val hi
        refine ⟨⟨i, ?_⟩, ?_⟩
        · rw [he]
          exact a.val.property
        · apply Subtype.ext
          exact Subtype.ext he)

theorem rimIncident_card
    (hu : ∀ s ∈ u, s ∉ Set.range C.edge) (hv : ∀ s ∈ v, s ∉ Set.range C.edge)
    (a : G.RimDart C) : Fintype.card (G.RimIncident C a.val.vertex) = 2 := by
  classical
  rcases a with ⟨a, ha⟩
  cases a with
  | top i => exact (hu _ (List.get_mem u i) ha).elim
  | bottom i => exact (hv _ (List.get_mem v i) ha).elim
  | hub h i =>
    change Fintype.card (G.RimIncident C (.inr (.inl h))) = 2
    change Fin 3 at i
    rw [SolutionGroup.rowGraph_port_label] at ha
    have hin : A.column (G.hubLabel h) i ∈ A.hypergraph.incidence (G.hubLabel h) :=
      (A.mem_hypergraph_incidence _ _).mpr ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := C.closed ha hin
    rw [← Fintype.card_congr (G.rimIncidentEquiv C (.inr (.inl h)))]
    change Fintype.card {k : Fin 3 //
      Port.label G.jointLabel (.hub h k : G.Dart) ∈ Set.range C.edge} = 2
    simp_rw [SolutionGroup.rowGraph_port_label]
    rw [← hj]
    exact C.row_rim_card j
  | joint j side =>
    change Fintype.card (G.RimIncident C (.inr (.inr j))) = 2
    rw [← Fintype.card_congr (G.rimIncidentEquiv C (.inr (.inr j)))]
    change Fintype.card {s : Bool // G.jointLabel j ∈ Set.range C.edge} = 2
    change G.jointLabel j ∈ Set.range C.edge at ha
    simp [ha]

end ThomGame.Pictures.PortGraph
