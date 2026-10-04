module

public import ThomGame.Pictures.SunRimSectors

/-!
# Planarity excludes the opposite rim orientations at a same-rim spoke

Both ends of the spoke lie on the same cut side. At each rim vertex,
that side is the xor of the hub orientation and outgoing rim slot.
Equal hub orientations therefore force equal outgoing slots. This is
derived from the actual simple-circuit separation theorem.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv RibbonConnectivity

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  (G : PortGraph (sunPresentation n b) u v) (hn : 3 ≤ n)
  (hu : ∀ z ∈ u, ∃ j, z = Sum.inl j) (hv : ∀ z ∈ v, ∃ j, z = Sum.inl j)

theorem sunRimCircuit_dart_at_hub (a : G.SunRimDart hn)
    (i : Fin (G.sunRimSimpleCircuit hn hu hv a).length) (h : G.Hub)
    (hvertex : ((G.sunRimSimpleCircuit hn hu hv a).dart i).vertex = .inr (.inl h)) :
    ∃ side, (G.sunRimSimpleCircuit hn hu hv a).dart i = (G.sunRimPort hn h side).val := by
  have hr := (G.sunRowGraph hn).rimSimpleCircuit_rim (Hypergraph.sunCycle n hn)
    (sunBoundary_no_rim hn hu) (sunBoundary_no_rim hn hv) a i
  change Port.label G.jointLabel ((G.sunRimSimpleCircuit hn hu hv a).dart i) ∈ _ at hr
  generalize he : (G.sunRimSimpleCircuit hn hu hv a).dart i = x at hvertex hr ⊢
  cases x with
  | top k => cases hvertex
  | bottom k => cases hvertex
  | joint j side => cases hvertex
  | hub k j =>
    have hk : k = h := Sum.inl.inj (Sum.inr.inj hvertex)
    subst k
    change Fin 3 at j
    fin_cases j
    · obtain ⟨l, hl⟩ := hr
      cases hl
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩

namespace SunSpoke

variable {G} (s : G.SunSpoke)

theorem rim_connected_same_orientation
    (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
      2 * Nat.card (Component G.circuitStep G.pairing.perm))
    (hf : G.hubFlip s.left = G.hubFlip s.right)
    (hc : Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm
      (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true)) :
    (G.sunRimWalk hn hu hv).SameCycle (G.sunRimPort hn s.left true) (G.sunRimPort hn s.right true) := by
  let a := G.sunRimPort hn s.left true
  let z := G.sunRimPort hn s.right true
  let C := G.sunRimSimpleCircuit hn hu hv a
  have hc' : (G.sunRowGraph hn).rimComponent (Hypergraph.sunCycle n hn)
      (sunBoundary_no_rim hn hu) (sunBoundary_no_rim hn hv) a =
    (G.sunRowGraph hn).rimComponent (Hypergraph.sunCycle n hn)
      (sunBoundary_no_rim hn hu) (sunBoundary_no_rim hn hv) z := (component_eq_iff _ _ _ _).mpr hc
  obtain ⟨i, hi, _⟩ := (G.sunRowGraph hn).rimSimpleCircuit_vertex_complete (Hypergraph.sunCycle n hn)
    (sunBoundary_no_rim hn hu) (sunBoundary_no_rim hn hv) a z hc'
  obtain ⟨side, hout⟩ := G.sunRimCircuit_dart_at_hub hn hu hv a i s.right hi
  have hL := G.sunRimCircuit_spoke_onSide hn hu hv a 0 s.left true rfl
  have hR := G.sunRimCircuit_spoke_onSide hn hu hv a i s.right side hout
  have huL := G.sunRimCircuit_spoke_unmarked hn hu hv a s.left
  have hL' : C.OnSide (xor (G.hubFlip s.left) true) (.hub s.right (0 : Fin 3)) := by
    have hp := (C.onSide_twin_iff huL (xor (G.hubFlip s.left) true)).mpr hL
    exact s.paired ▸ hp
  have he := C.onSide_unique hEuler hL' hR
  have hside : side = true := by
    rw [hf] at he
    cases side <;> cases hfr : G.hubFlip s.right <;> simp_all
  subst side
  have hi' : OrbitEnumeration.dart (G.sunRimWalk hn hu hv) a i = z := Subtype.ext hout
  change (G.sunRimWalk hn hu hv).SameCycle a z
  exact hi' ▸ OrbitEnumeration.dart_sameCycle (G.sunRimWalk hn hu hv) a i

end SunSpoke
end ThomGame.Pictures.PortGraph
