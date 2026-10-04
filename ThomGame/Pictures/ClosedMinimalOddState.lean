module

public import ThomGame.Pictures.GraphComponentDiagrams
public import ThomGame.Pictures.MinimalRegionDiagrams
public import ThomGame.Pictures.ReducedMinimalRecovery

/-!
# Minimal odd states on actual closed graphs

Minimality compares the actual hub count with genuine odd closed
diagrams. It does not identify the graph with a diagram witness.
Component extraction proves hub connectivity from this minimality.
Consequently the original graph has minimal region and germ witnesses,
and a zero-sign germ whenever the circuit has zero parity.
-/

@[expose] public section
namespace ThomGame.Pictures

open RibbonConnectivity
open scoped Classical BigOperators

variable {R S : Type*} {P : InvolutionPresentation R S}

namespace PortGraph

structure ClosedMinimalOddState (G : PortGraph P [] []) : Prop where
  euler : eulerDefect G.pairing.perm G.circuitStep = 0
  sign : G.sign = 1
  minimal : ∀ e : Diagram P [] [], e.sign = 1 → Fintype.card G.Hub ≤ e.size

namespace ClosedMinimalOddState

variable {G : PortGraph P [] []} (h : G.ClosedMinimalOddState)

theorem of_witness (he : eulerDefect G.pairing.perm G.circuitStep = 0)
    (hs : G.sign = 1) (d : Diagram P [] []) (hmin : d.Minimal)
    (hsize : d.size = Fintype.card G.Hub) (hsign : d.sign = 1) :
    G.ClosedMinimalOddState where
  euler := he
  sign := hs
  minimal e hes := hsize ▸ hmin e (hes.trans hsign.symm)

include h

theorem exists_minimal_diagram (hn : ∀ x, 0 < (P.word (G.hubLabel x)).length) :
    ∃ d : Diagram P [] [],
      (d.labels : Multiset R) = (∑ x : G.Hub, ([G.hubLabel x] : Multiset R)) ∧
      d.size = Fintype.card G.Hub ∧ d.sign = 1 ∧ d.Minimal := by
  obtain ⟨d, hd, hn', hs⟩ := G.exists_closed_diagram_of_saturated_preserving hn
    (G.rotationEuler_saturated_iff.mpr h.euler)
  have hs' := hs.trans h.sign
  exact ⟨d, hd, hn', hs', fun e he => hn'.trans_le (h.minimal e (he.trans hs'))⟩

theorem hubs_in_odd_component (hn : ∀ x, 0 < (P.word (G.hubLabel x)).length)
    (k : G.GraphComponent) (hk : G.componentWeight k P.parity = 1) :
    ∀ x : G.Hub, G.hubComponent x = k := by
  obtain ⟨e, _, hn', hs⟩ := G.exists_component_diagram hn
    (G.rotationEuler_saturated_iff.mpr h.euler) k
  have hle := h.minimal e (hs.trans hk)
  rw [hn'] at hle
  intro x
  by_contra hx
  have hlt : G.componentWeight k (fun _ => (1 : Nat)) < Fintype.card G.Hub := by
    unfold componentWeight
    calc
      (∑ y : G.Hub, if G.hubComponent y = k then 1 else 0) <
          ∑ _ : G.Hub, (1 : Nat) := by
        apply Finset.sum_lt_sum
        · intro y _; split <;> omega
        · exact ⟨x, Finset.mem_univ _, by simp [hx]⟩
      _ = Fintype.card G.Hub := by simp
  exact (Nat.not_lt_of_ge hle) hlt

theorem hubs_reachable (hn : ∀ x, 0 < (P.word (G.hubLabel x)).length)
    (x y : G.Hub) : G.Reachable (.inr (.inl x)) (.inr (.inl y)) := by
  obtain ⟨k, hk⟩ := G.exists_odd_component h.sign
  exact (G.graphComponent_eq_iff _ _).mp
    ((h.hubs_in_odd_component hn k hk x).trans (h.hubs_in_odd_component hn k hk y).symm)

theorem vertices_reachable [IsEmpty G.Joint]
    (hn : ∀ x, 0 < (P.word (G.hubLabel x)).length) :
    ∀ x y : G.Vertex, G.Reachable x y :=
  G.closed_reachable_of_hubs (h.hubs_reachable hn)

theorem dualEuler : RotationEuler.count G.circuitStep G.pairing.perm =
    2 * Nat.card (Component G.circuitStep G.pairing.perm) :=
  G.dualEuler_eq_twice_components h.euler

theorem exists_minimal_circuit_diagrams
    (hn : ∀ x, 0 < (P.word (G.hubLabel x)).length) (C : G.SimpleCircuit) (s : Bool) :
    ∃ g : Diagram P [] (C.frontierWord (!s)), ∃ e : Diagram P (C.frontierWord (!s)) [],
      (g.labels : Multiset R) = (∑ x : C.GermHub s, ([G.hubLabel x.val] : Multiset R)) ∧
      (e.labels : Multiset R) = (∑ x : C.InteriorHub (!s), ([G.hubLabel x.val] : Multiset R)) ∧
      g.size = Fintype.card (C.GermHub s) ∧ e.size = Fintype.card (C.InteriorHub (!s)) ∧
      g.sign = (C.germGraph h.dualEuler s).sign ∧
      e.sign = (C.regionGraph h.dualEuler (!s)).sign ∧ g.Minimal ∧ e.Minimal := by
  obtain ⟨d, _, hdsize, hdsign, hdmin⟩ := h.exists_minimal_diagram hn
  obtain ⟨g, hgl, hgs, hg⟩ := C.exists_germ_diagram_preserving h.dualEuler s (fun x => hn x.val)
  obtain ⟨e, hel, hes, he⟩ := C.exists_region_diagram_preserving h.dualEuler (!s) (fun x => hn x.val)
  have hm := C.germ_region_witnesses_minimal h.dualEuler d hdmin hdsize.symm
    (h.sign.trans hdsign.symm) (h.hubs_reachable hn) s g e hgs hes hg he
  exact ⟨g, e, hgl, hel, hgs, hes, hg, he, hm⟩

theorem exists_minimal_zero_sign_germ
    (hn : ∀ x, 0 < (P.word (G.hubLabel x)).length) (C : G.SimpleCircuit)
    (hC : (∑ x : C.CircuitHub, P.parity (G.hubLabel x.val)) = 0) :
    ∃ s, ∃ g : Diagram P [] (C.frontierWord (!s)),
      (g.labels : Multiset R) = (∑ x : C.GermHub s, ([G.hubLabel x.val] : Multiset R)) ∧
      g.size = Fintype.card (C.GermHub s) ∧ g.sign = 0 ∧ g.Minimal ∧
      (C.germGraph h.dualEuler s).sign = 0 := by
  obtain ⟨s, hs⟩ := C.exists_germ_sign_zero_of_hubs_reachable h.dualEuler
    (h.hubs_reachable hn) h.sign hC
  obtain ⟨g, _, hgl, _, hgs, _, hg, _, hgm, _⟩ := h.exists_minimal_circuit_diagrams hn C s
  exact ⟨s, g, hgl, hgs, hg.trans hs, hgm, hs⟩

end ClosedMinimalOddState
end PortGraph

namespace Smoothing

variable {d : Diagram P [] []} {G : PortGraph P [] []} {circles : List S}
    (t : Smoothing d.graph G circles)

include t in
theorem closedMinimalOddState (hmin : d.Minimal) (hs : d.sign = 1)
    (hn : ∀ x : d.graph.Hub, 0 < (P.word (d.graph.hubLabel x)).length) :
    G.ClosedMinimalOddState :=
  .of_witness (t.diagram_eulerDefect hn) (t.sign.trans (d.graph_sign.trans hs))
    d hmin (t.hub_card.trans d.graph_hub_card).symm hs

end Smoothing
end ThomGame.Pictures
