module

public import ThomGame.Pictures.GraphBoundaryComponents
public import ThomGame.Pictures.ComponentEuler
public import ThomGame.Pictures.CircuitTrace

/-!
# Vertex components and the actual integer Euler expression

The permutation component quotient embeds into the quotient of actual
vertex paths. If every hub has at least one port, it is a bijection.
Rotation and edge orbits are likewise identified with actual vertices
and edges. This reconciles the generic counts with `PortGraph.ribbonEuler`;
it does not assert that this number equals twice the components.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv FiniteReturn

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S} (G : PortGraph P u v)

def graphComponentSetoid : Setoid G.Vertex where
  r := G.Reachable
  iseqv := ⟨G.reachable_refl, G.reachable_symm, G.reachable_trans⟩

def GraphComponent := Quotient G.graphComponentSetoid

instance : Finite G.GraphComponent := by unfold GraphComponent; infer_instance

def graphComponent (x : G.Vertex) : G.GraphComponent := Quotient.mk _ x

theorem graphComponent_eq_iff (x y : G.Vertex) :
    G.graphComponent x = G.graphComponent y ↔ G.Reachable x y := Quotient.eq

def dartComponentMap : RibbonConnectivity.Component G.pairing.perm G.circuitStep → G.GraphComponent :=
  Quotient.lift (fun a => G.graphComponent a.vertex) (fun x y h =>
    (G.graphComponent_eq_iff x.vertex y.vertex).mpr (G.connected_vertex_reachable h))

theorem dartComponentMap_injective : Function.Injective G.dartComponentMap := by
  intro c d hcd
  refine Quotient.inductionOn₂ c d (fun a b he => ?_) hcd
  apply (RibbonConnectivity.component_eq_iff G.pairing.perm G.circuitStep a b).mpr
  exact (G.connected_iff_vertex_reachable a b).mpr ((G.graphComponent_eq_iff _ _).mp he)

theorem exists_dart_at (hn : ∀ h : G.Hub, 0 < (P.word (G.hubLabel h)).length) (x : G.Vertex) :
    ∃ a : G.Dart, a.vertex = x := by
  rcases x with (i | i) | (h | j)
  · exact ⟨.top i, rfl⟩
  · exact ⟨.bottom i, rfl⟩
  · exact ⟨.hub h ⟨0, hn h⟩, rfl⟩
  · exact ⟨.joint j false, rfl⟩

noncomputable def dartComponentEquiv (hn : ∀ h : G.Hub, 0 < (P.word (G.hubLabel h)).length) :
    RibbonConnectivity.Component G.pairing.perm G.circuitStep ≃ G.GraphComponent :=
  Equiv.ofBijective G.dartComponentMap ⟨G.dartComponentMap_injective, by
    intro c
    refine Quotient.inductionOn c fun x => ?_
    obtain ⟨a, ha⟩ := G.exists_dart_at hn x
    exact ⟨RibbonConnectivity.component G.pairing.perm G.circuitStep a, congrArg G.graphComponent ha⟩⟩

def rotationVertex : Orbit G.rotation → G.Vertex :=
  Quotient.lift Port.vertex (fun a b h => (G.rotation_sameCycle_iff a b).mp h)

theorem rotationVertex_injective : Function.Injective G.rotationVertex := by
  intro c d hcd
  refine Quotient.inductionOn₂ c d (fun a b he => ?_) hcd
  exact (orbit_eq_iff G.rotation a b).mpr ((G.rotation_sameCycle_iff a b).mpr he)

noncomputable def rotationVertexEquiv (hn : ∀ h : G.Hub, 0 < (P.word (G.hubLabel h)).length) :
    Orbit G.rotation ≃ G.Vertex :=
  Equiv.ofBijective G.rotationVertex ⟨G.rotationVertex_injective, by
    intro x
    obtain ⟨a, ha⟩ := G.exists_dart_at hn x
    exact ⟨orbit G.rotation a, ha⟩⟩

theorem pairing_sameCycle_iff_edge (a b : G.Dart) :
    G.pairing.perm.SameCycle a b ↔ G.pairing.edge a = G.pairing.edge b := by
  rw [CircularPartition.involutive_sameCycle G.pairing.perm G.pairing.involutive a b,
    G.pairing.edge_eq_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h.symm
    · change b = G.pairing.twin a at h
      exact Or.inr (by change a = G.pairing.twin b; rw [h, G.pairing.involutive])
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr (by change b = G.pairing.twin a; rw [h, G.pairing.involutive])

def edgeOrbitEquiv : Orbit G.pairing.perm ≃ G.Edge where
  toFun := Quotient.lift G.pairing.edge (fun a b h => (G.pairing_sameCycle_iff_edge a b).mp h)
  invFun := Quotient.lift (orbit G.pairing.perm) (fun a b h =>
    (orbit_eq_iff _ _ _).mpr ((G.pairing_sameCycle_iff_edge a b).mpr (Quotient.sound h)))
  left_inv c := Quotient.inductionOn c (fun _ => rfl)
  right_inv c := Quotient.inductionOn c (fun _ => rfl)

theorem circuit_mul_pairing : G.circuitStep * G.pairing.perm = G.rotation := by
  ext a
  change G.rotation (G.pairing.twin (G.pairing.twin a)) = G.rotation a
  rw [G.pairing.involutive]

theorem eulerCount_eq_ribbonEuler (hn : ∀ h : G.Hub, 0 < (P.word (G.hubLabel h)).length) :
    RibbonConnectivity.eulerCount G.pairing.perm G.circuitStep = G.ribbonEuler := by
  classical
  unfold RibbonConnectivity.eulerCount ribbonEuler
  rw [G.circuit_mul_pairing, Nat.card_congr (G.rotationVertexEquiv hn),
    Nat.card_congr G.edgeOrbitEquiv]
  change (Nat.card G.Vertex : Int) - Nat.card G.Edge + Nat.card G.Circuit = _
  simp only [Nat.card_eq_fintype_card]

theorem eulerDefect_eq_ribbonEuler (hn : ∀ h : G.Hub, 0 < (P.word (G.hubLabel h)).length) :
    RibbonConnectivity.eulerDefect G.pairing.perm G.circuitStep =
      G.ribbonEuler - 2 * Nat.card G.GraphComponent := by
  classical
  unfold RibbonConnectivity.eulerDefect
  rw [G.eulerCount_eq_ribbonEuler hn, Nat.card_congr (G.dartComponentEquiv hn)]

end ThomGame.Pictures.PortGraph
