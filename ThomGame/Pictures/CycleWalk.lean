module

public import ThomGame.Pictures.CycleRestriction
public import ThomGame.Pictures.RibbonConnectivity

/-!
# The unique continuation through a restricted cycle vertex

Exactly two retained ports at each vertex give a fixed-point-free local
involution. Together with the actual edge pairing this defines the rim
walk and its finite connected components. These components describe
the restricted finite graph; no disk-bounding or facial claim is used.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

variable {R S : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
  {u v : List S} (G : SolutionGroup.RowGraph A u v) (C : Hypergraph.Cycle A.hypergraph)
  (hu : ∀ s ∈ u, s ∉ Set.range C.edge) (hv : ∀ s ∈ v, s ∉ Set.range C.edge)

include hu hv

theorem existsUnique_rim_neighbour (a : G.RimDart C) :
    ∃! b : G.RimDart C, b.val.vertex = a.val.vertex ∧ b ≠ a := by
  classical
  let a₀ : G.RimIncident C a.val.vertex := ⟨a, rfl⟩
  have hc : (Finset.univ.erase a₀).card = 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ a₀), Finset.card_univ,
      G.rimIncident_card C hu hv a]
  have hn : ∃! b : G.RimIncident C a.val.vertex, b ≠ a₀ := by
    simpa using (Finset.card_eq_one_iff_existsUnique.mp hc)
  obtain ⟨b, hb, huniq⟩ := hn
  refine ⟨b.val, ⟨b.property, fun he => hb (Subtype.ext he)⟩, ?_⟩
  intro c hc
  have hc' : (⟨c, hc.1⟩ : G.RimIncident C a.val.vertex) ≠ a₀ :=
    fun he => hc.2 (congrArg Subtype.val he)
  exact congrArg Subtype.val (huniq ⟨c, hc.1⟩ hc')

noncomputable def rimSwitch (a : G.RimDart C) : G.RimDart C :=
  Classical.choose (G.existsUnique_rim_neighbour C hu hv a)

theorem rimSwitch_vertex (a : G.RimDart C) :
    (G.rimSwitch C hu hv a).val.vertex = a.val.vertex :=
  (Classical.choose_spec (G.existsUnique_rim_neighbour C hu hv a)).1.1

theorem rimSwitch_ne_self (a : G.RimDart C) : G.rimSwitch C hu hv a ≠ a :=
  (Classical.choose_spec (G.existsUnique_rim_neighbour C hu hv a)).1.2

theorem rimSwitch_unique (a b : G.RimDart C)
    (hb : b.val.vertex = a.val.vertex) (hne : b ≠ a) : b = G.rimSwitch C hu hv a :=
  (Classical.choose_spec (G.existsUnique_rim_neighbour C hu hv a)).2 b ⟨hb, hne⟩

theorem rimSwitch_involutive : Function.Involutive (G.rimSwitch C hu hv) := by
  intro a
  exact (G.rimSwitch_unique C hu hv (G.rimSwitch C hu hv a) a
    (G.rimSwitch_vertex C hu hv a).symm (Ne.symm (G.rimSwitch_ne_self C hu hv a))).symm

noncomputable def rimVertexPairing : Pairing (fun a : G.RimDart C => a.val.vertex) where
  twin := G.rimSwitch C hu hv
  involutive := G.rimSwitch_involutive C hu hv
  ne_self := G.rimSwitch_ne_self C hu hv
  label_twin := G.rimSwitch_vertex C hu hv

theorem rim_same_vertex_iff (a b : G.RimDart C) :
    a.val.vertex = b.val.vertex ↔ a = b ∨ a = G.rimSwitch C hu hv b := by
  classical
  constructor
  · intro hab
    by_cases he : a = b
    · exact Or.inl he
    · exact Or.inr (G.rimSwitch_unique C hu hv b a hab he)
  · rintro (rfl | rfl)
    · rfl
    · exact G.rimSwitch_vertex C hu hv b

theorem rimVertexPairing_eq_iff (a b : G.RimDart C) :
    (G.rimVertexPairing C hu hv).edge a = (G.rimVertexPairing C hu hv).edge b ↔
      a.val.vertex = b.val.vertex := by
  rw [Pairing.edge_eq_iff, G.rim_same_vertex_iff C hu hv]
  rfl

noncomputable def rimWalk : Equiv.Perm (G.RimDart C) :=
  (G.rimPairing C).perm.trans (G.rimVertexPairing C hu hv).perm

theorem rimWalk_vertex (a : G.RimDart C) :
    (G.rimWalk C hu hv a).val.vertex = (G.pairing.twin a.val).vertex :=
  G.rimSwitch_vertex C hu hv ((G.rimPairing C).twin a)

def RimComponent :=
  RibbonConnectivity.Component (G.rimPairing C).perm (G.rimVertexPairing C hu hv).perm

noncomputable instance : Fintype (G.RimComponent C hu hv) := by
  unfold RimComponent
  exact Fintype.ofFinite _

noncomputable def rimComponent (a : G.RimDart C) : G.RimComponent C hu hv :=
  RibbonConnectivity.component _ _ a

theorem rimComponent_twin (a : G.RimDart C) :
    G.rimComponent C hu hv ((G.rimPairing C).twin a) = G.rimComponent C hu hv a :=
  RibbonConnectivity.component_edge _ _ a

theorem rimComponent_vertex {a b : G.RimDart C} (hab : a.val.vertex = b.val.vertex) :
    G.rimComponent C hu hv a = G.rimComponent C hu hv b := by
  rcases (G.rim_same_vertex_iff C hu hv a b).mp hab with rfl | rfl
  · rfl
  · exact RibbonConnectivity.component_circuit _ _ b

end ThomGame.Pictures.PortGraph
