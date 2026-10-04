module

public import ThomGame.Pictures.SunFacialCovers

/-!
# Normalizing an actual connected minimal sun graph

Minimum size excludes a nonempty closed component. Connectedness then
supplies boundary accessibility directly on the input port graph. The
finite switch algorithm can start from this graph without identifying
it with the graph of any diagram witness.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SunMinimalState

open RibbonConnectivity
open scoped BigOperators

variable {n : Nat} {b : Fin n → ZMod 2} {w : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) [] w} (h : G.SunMinimalState)
  (hconn : ∀ a c : G.Dart, Connected G.rotation G.pairing.perm a c)

include h hconn in
theorem hubsReachBoundary_of_connected : G.HubsReachBoundary := by
  intro x
  have hw : 0 < w.length := by
    by_contra hn
    have he : w = [] := List.length_eq_zero_iff.mp (by omega)
    subst w
    have hm := h.minimal (.identity [])
    have hp : 0 < Fintype.card G.Hub := Fintype.card_pos_iff.mpr ⟨x⟩
    change Fintype.card G.Hub ≤ 0 at hm
    omega
  let j : Fin w.length := ⟨0, hw⟩
  have hc := (RotationEuler.connected_rotation_iff G.rotation G.pairing.perm G.pairing.involutive
    (.hub x (0 : Fin 3)) (G.boundaryDart (.inr j))).mp (hconn _ _)
  rw [G.rotation_mul_pairing] at hc
  have hr := G.connected_vertex_reachable hc
  rw [G.boundaryDart_vertex] at hr
  exact ⟨.inr j, hr⟩

variable [IsEmpty G.Joint] (hn : 3 ≤ n) (hw : ∀ z ∈ w, ∃ j, z = Sum.inl j)

include h hconn in
theorem exists_facial_cover_switches_of_connected :
    ∃ (H : PortGraph (sunPresentation n b) [] w) (q : SunSwitchTrace G H),
      q.Inward hn hw ∧ H.SunFaceState hn hw ∧ H.SunRimsFacialCovers hn hw ∧
      (∑ x : H.Hub, ([H.hubLabel x] : Multiset (Fin n))) =
        (∑ x : G.Hub, ([G.hubLabel x] : Multiset (Fin n))) ∧
      Fintype.card H.Hub = Fintype.card G.Hub ∧ H.sign = G.sign := by
  have hb := h.hubsReachBoundary_of_connected hconn
  have hr := fun a : G.SunRimDart hn =>
    (G.sunRimSimpleCircuit hn (by simp) hw a).meetsBoundary_of_hubsReachBoundary hb
  obtain ⟨H, q, hq, hNo⟩ := h.exists_no_interior_spoke hn hw hr
  have hf : H.SunFaceState hn hw := SunFaceState.of_terminal hn hw
    (q.minimalState h) (q.isEmpty_joints inferInstance) (q.hubsReachBoundary hb) hNo
  exact ⟨H, q, hq, hf, hf.facial_covers hn hw, q.hub_relations, q.hub_card, q.sign⟩

end ThomGame.Pictures.PortGraph.SunMinimalState
