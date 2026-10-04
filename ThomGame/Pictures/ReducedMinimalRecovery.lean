module

public import ThomGame.Pictures.MinimalSmoothedGerm
public import ThomGame.Pictures.CircuitGermRecovery

/-!
# Recovery of the whole reduced minimal odd graph

In a closed graph without joints every vertex is a relation hub. Thus
the reduced graph of a minimal odd diagram is connected. The existing
germ-region smoothing then recovers every original dart, not only a
possibly proper component. This remains a port-graph statement.
-/

@[expose] public section
namespace ThomGame.Pictures

open RibbonConnectivity
open scoped BigOperators Classical

variable {R S : Type*} {P : InvolutionPresentation R S}

namespace PortGraph

theorem closed_reachable_of_hubs (G : PortGraph P [] []) [IsEmpty G.Joint]
    (hc : ∀ h k : G.Hub, G.Reachable (.inr (.inl h)) (.inr (.inl k))) :
    ∀ x y : G.Vertex, G.Reachable x y := by
  intro x y
  rcases x with (i | i) | (h | j)
  · exact i.elim0
  · exact i.elim0
  · rcases y with (i | i) | (k | j)
    · exact i.elim0
    · exact i.elim0
    · exact hc h k
    · exact isEmptyElim j
  · exact isEmptyElim j

namespace SimpleCircuit

variable {G : PortGraph P [] []} (C : G.SimpleCircuit)
  (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
    2 * Nat.card (Component G.circuitStep G.pairing.perm))
  (hc : ∀ x y : G.Vertex, G.Reachable x y)

include hc in
theorem all_ports_in_component (a : G.Dart) : Connected G.circuitStep G.pairing.perm a C.cutBase :=
  (RotationEuler.connected_swap_iff G.circuitStep G.pairing.perm _ _).mpr
    ((G.connected_iff_vertex_reachable _ _).mpr (hc a.vertex C.cutBase.vertex))

noncomputable def recoveredAllPorts (s : Bool) : (C.germReduction hEuler s).graph.Dart ≃ G.Dart where
  toFun a := (C.recoveredPorts hEuler s a).val
  invFun a := (C.recoveredPorts hEuler s).symm ⟨a, C.all_ports_in_component hc a⟩
  left_inv a := by
    apply (C.recoveredPorts hEuler s).injective
    exact ((C.recoveredPorts hEuler s).apply_symm_apply _).trans (Subtype.ext rfl)
  right_inv a := congrArg Subtype.val ((C.recoveredPorts hEuler s).apply_symm_apply _)

include hEuler hc in
theorem recoveredAllPorts_twin (s : Bool) (a : (C.germReduction hEuler s).graph.Dart) :
    C.recoveredAllPorts hEuler hc s ((C.germReduction hEuler s).graph.pairing.twin a) =
      G.pairing.twin (C.recoveredAllPorts hEuler hc s a) := C.recoveredPorts_twin hEuler s a

include hEuler hc in
theorem recoveredAllPorts_label (s : Bool) (a : (C.germReduction hEuler s).graph.Dart) :
    Port.label G.jointLabel (C.recoveredAllPorts hEuler hc s a) =
      Port.label (C.germReduction hEuler s).graph.jointLabel a := C.recoveredPorts_label hEuler s a

include hEuler hc in
theorem recoveredAllPorts_rotation (s : Bool) (a : (C.germReduction hEuler s).graph.Dart) :
    C.recoveredAllPorts hEuler hc s ((C.germReduction hEuler s).graph.rotation a) =
      G.rotation (C.recoveredAllPorts hEuler hc s a) := C.recoveredPorts_rotation hEuler s a

include hEuler hc in
theorem recoveredAllPorts_vertex_iff (s : Bool) (a b : (C.germReduction hEuler s).graph.Dart) :
    a.vertex = b.vertex ↔ (C.recoveredAllPorts hEuler hc s a).vertex =
      (C.recoveredAllPorts hEuler hc s b).vertex := C.recoveredPorts_vertex_iff hEuler s a b

include hEuler hc in
theorem recoveredAllPorts_edge_iff (s : Bool) (a b : (C.germReduction hEuler s).graph.Dart) :
    (C.germReduction hEuler s).graph.pairing.edge a = (C.germReduction hEuler s).graph.pairing.edge b ↔
      G.pairing.edge (C.recoveredAllPorts hEuler hc s a) =
        G.pairing.edge (C.recoveredAllPorts hEuler hc s b) := C.recoveredPorts_edge_iff hEuler s a b

include hEuler hc in
theorem germReduction_sign_of_connected (s : Bool) : (C.germReduction hEuler s).graph.sign = G.sign := by
  rw [C.germReduction_sign]
  trans ∑ h : G.Hub, if C.InCircuitComponent (.inr (.inl h)) then P.parity (G.hubLabel h) else 0
  · exact subtype_sum_indicator (fun h : G.Hub => C.InCircuitComponent (.inr (.inl h)))
      (fun h => P.parity (G.hubLabel h))
  apply Finset.sum_congr rfl
  intro h _
  have hx : C.InCircuitComponent (.inr (.inl h)) :=
    (C.inCircuitComponent_iff_reachable _).mpr (hc _ _)
  simp only [hx, ite_true]

include hEuler hc in
theorem germReduction_character_of_connected [DecidableEq R] (s : Bool) (r : R) :
    (C.germReduction hEuler s).graph.character r = G.character r := by
  rw [C.germReduction_character, G.character_eq_sum]
  trans ∑ h : G.Hub, if C.InCircuitComponent (.inr (.inl h)) then
    (if G.hubLabel h = r then (1 : ZMod 2) else 0) else 0
  · exact subtype_sum_indicator (fun h : G.Hub => C.InCircuitComponent (.inr (.inl h)))
      (fun h => if G.hubLabel h = r then (1 : ZMod 2) else 0)
  apply Finset.sum_congr rfl
  intro h _
  have hx : C.InCircuitComponent (.inr (.inl h)) :=
    (C.inCircuitComponent_iff_reachable _).mpr (hc _ _)
  simp only [hx, ite_true]

end SimpleCircuit
end PortGraph

namespace Smoothing

variable {d : Diagram P [] []} {H : PortGraph P [] []} {circles : List S}
  (t : Smoothing d.graph H circles) [IsEmpty H.Joint]
  (hmin : d.Minimal) (hs : d.sign = 1)
  (hn : ∀ h : d.graph.Hub, 0 < (P.word (d.graph.hubLabel h)).length)

include t hmin hs hn in
theorem minimal_odd_reduced_reachable : ∀ x y : H.Vertex, H.Reachable x y :=
  H.closed_reachable_of_hubs (t.minimal_odd_hubs_reachable hmin hs hn)

noncomputable def minimal_odd_recoveredAllPorts (C : H.SimpleCircuit) (s : Bool) :
    (C.germReduction (t.diagram_dualEuler hn) s).graph.Dart ≃ H.Dart :=
  C.recoveredAllPorts (t.diagram_dualEuler hn) (t.minimal_odd_reduced_reachable hmin hs hn) s

end Smoothing
end ThomGame.Pictures
