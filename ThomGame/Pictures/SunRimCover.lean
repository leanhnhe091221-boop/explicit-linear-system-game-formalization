module

public import ThomGame.Pictures.SunFaceTermination
public import ThomGame.Pictures.SunEdgeCancellation

/-!
# The rims of an actual terminal minimal sun graph are covers

Every rim edge has two hub endpoints with different relation labels,
as required by the paper's definition of a cover. Equal labels would
force equal port slots. Minimality forces equal hub orientations across
such an edge, while the common exterior side of a facial rim forces
opposite orientations. Both statements concern the actual paired darts.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv RibbonConnectivity
open scoped Classical

namespace SimpleCircuit

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  {G : PortGraph P u v} (C : G.SimpleCircuit)

/-- Every circuit edge has two hub endpoints with distinct relation labels. -/
def IsLabelCover : Prop :=
  ∀ i : Fin C.length, ∃ (h k : G.Hub)
      (p : Fin (P.word (G.hubLabel h)).length) (q : Fin (P.word (G.hubLabel k)).length),
    C.dart i = .hub h p ∧ G.pairing.twin (C.dart i) = .hub k q ∧
      h ≠ k ∧ G.hubLabel h ≠ G.hubLabel k

theorem side_eq_boundarySide_of_not_interior
    (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
      2 * Nat.card (Component G.circuitStep G.pairing.perm))
    (hsees : G.BoundarySeesComponents) (hb : C.MeetsBoundary)
    {side : Bool} {x : G.Dart} (hs : C.OnSide side x) (hi : ¬ C.CutInterior x) :
    side = C.boundarySide hb := by
  have hn : side ≠ (!C.boundarySide hb) := by
    intro he
    exact hi ((C.on_opposite_boundarySide_iff hEuler hsees hb x).mp (he ▸ hs))
  cases side <;> cases hB : C.boundarySide hb <;> simp_all

end SimpleCircuit

variable {n : Nat} {b : Fin n → ZMod 2} {w : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) [] w} (hn : 3 ≤ n)
  (hw : ∀ z ∈ w, ∃ j, z = Sum.inl j)

include hn in
theorem sun_same_label_paired_slot (h k : G.Hub) (i j : Fin 3)
    (he : G.pairing.twin (.hub h i) = .hub k j) (hl : G.hubLabel h = G.hubLabel k) : i = j := by
  have hp := G.pairing.label_twin (.hub h i)
  rw [he] at hp
  have hq : Port.label G.jointLabel (.hub h i : G.Dart) = Port.label G.jointLabel (.hub h j : G.Dart) :=
    hp.symm.trans (G.sun_same_hubLabel_port_label hl j).symm
  apply (Hypergraph.sunSystem n hn b).column_injective (G.hubLabel h)
  exact (SolutionGroup.rowGraph_port_label (Hypergraph.sunSystem n hn b) G h i).symm.trans
    (hq.trans (SolutionGroup.rowGraph_port_label (Hypergraph.sunSystem n hn b) G h j))

theorem sun_same_rim_slot_next (h k : G.Hub) (side : Bool)
    (he : G.pairing.twin (G.sunRimPort hn h side).val = (G.sunRimPort hn k side).val) :
    let C := G.sunRimSimpleCircuit hn (by simp) hw (G.sunRimPort hn h side)
    C.dart (finRotate C.length 0) = (G.sunRimPort hn k (!side)).val := by
  let a := G.sunRimPort hn h side
  have ht : (G.sunRimPairing hn).twin a = G.sunRimPort hn k side := Subtype.ext he
  have hd := OrbitEnumeration.dart_next (G.sunRimWalk hn (by simp) hw) a 0
  rw [OrbitEnumeration.dart_zero] at hd
  change OrbitEnumeration.dart (G.sunRimWalk hn (by simp) hw) a _ =
    (G.sunRimVertexPairing hn (by simp) hw).twin ((G.sunRimPairing hn).twin a) at hd
  rw [ht, G.sunRimVertexPairing_port] at hd
  exact congrArg Subtype.val hd

include hw in
theorem sunRimDart_exists_hub [IsEmpty G.Joint] (a : G.SunRimDart hn) :
    ∃ (h : G.Hub) (i : Fin 3), i ≠ 0 ∧ a.val = .hub h i := by
  rcases a with ⟨x, hx⟩
  cases x with
  | top i => exact i.elim0
  | bottom i =>
    obtain ⟨j, hj⟩ := hw w[i] (List.getElem_mem i.isLt)
    obtain ⟨k, hk⟩ := hx
    change Sum.inr k = w[i] at hk
    rw [hj] at hk
    cases hk
  | joint j side => exact (isEmptyElim j : False).elim
  | hub h i =>
    change Fin 3 at i
    fin_cases i
    · obtain ⟨j, hj⟩ := hx
      cases hj
    · exact ⟨h, 1, by decide +kernel, rfl⟩
    · exact ⟨h, 2, by decide +kernel, rfl⟩

namespace SunFaceState

variable (H : G.SunFaceState hn hw)

include H in
theorem same_rim_slot_flip_ne (h k : G.Hub) (side : Bool)
    (he : G.pairing.twin (G.sunRimPort hn h side).val = (G.sunRimPort hn k side).val) :
    G.hubFlip h ≠ G.hubFlip k := by
  let : IsEmpty G.Joint := H.noJoints
  let a := G.sunRimPort hn h side
  let C := G.sunRimSimpleCircuit hn (by simp) hw a
  have hd := G.sun_same_rim_slot_next hn hw h k side he
  have hh : C.OnCircuitVertex (.inr (.inl h)) := by
    refine ⟨0, ?_⟩
    cases side <;> rfl
  have hk : C.OnCircuitVertex (.inr (.inl k)) := by
    refine ⟨finRotate C.length 0, ?_⟩
    exact (congrArg Port.vertex hd).trans (by cases side <;> rfl)
  have hL := G.sunRimCircuit_spoke_onSide hn (by simp) hw a 0 h side rfl
  have hR := G.sunRimCircuit_spoke_onSide hn (by simp) hw a (finRotate C.length 0) k (!side) hd
  have hb := C.meetsBoundary_of_hubsReachBoundary H.boundary
  have hBL := C.side_eq_boundarySide_of_not_interior
    (G.dualEuler_eq_twice_components H.minimal.euler) H.minimal.sees hb hL
    (G.noInteriorSunSpoke_rim_hub hn hw H.terminal a h hh)
  have hBR := C.side_eq_boundarySide_of_not_interior
    (G.dualEuler_eq_twice_components H.minimal.euler) H.minimal.sees hb hR
    (G.noInteriorSunSpoke_rim_hub hn hw H.terminal a k hk)
  intro hf
  have heq := hBL.trans hBR.symm
  rw [hf] at heq
  cases side <;> cases hfK : G.hubFlip k <;> simp [hfK] at heq

include H in
theorem rim_edge_labels_ne (h k : G.Hub) (i j : Fin 3) (hi : i ≠ 0)
    (he : G.pairing.twin (.hub h i) = .hub k j) : G.hubLabel h ≠ G.hubLabel k := by
  intro hl
  have hij := G.sun_same_label_paired_slot hn h k i j he hl
  subst j
  have hf := H.minimal.same_flip_of_same_label_edge h k i he hl
  fin_cases i
  · exact hi rfl
  · exact H.same_rim_slot_flip_ne hn hw h k false he hf
  · exact H.same_rim_slot_flip_ne hn hw h k true he hf

include H in
theorem rim_isLabelCover (a : G.SunRimDart hn) :
    (G.sunRimSimpleCircuit hn (by simp) hw a).IsLabelCover := by
  let : IsEmpty G.Joint := H.noJoints
  let C := G.sunRimSimpleCircuit hn (by simp) hw a
  intro i
  let x : G.SunRimDart hn := ⟨C.dart i,
    G.sunRimCircuit_marked_rim hn (by simp) hw a ⟨(i, false), rfl⟩⟩
  obtain ⟨h, p, hp, hx⟩ := G.sunRimDart_exists_hub hn hw x
  obtain ⟨k, q, _, hy⟩ := G.sunRimDart_exists_hub hn hw ((G.sunRimPairing hn).twin x)
  have he : G.pairing.twin (.hub h p) = .hub k q :=
    (congrArg G.pairing.twin hx).symm.trans hy
  have hlabels := H.rim_edge_labels_ne hn hw h k p q hp he
  exact ⟨h, k, p, q, hx, hy, fun hhk => hlabels (congrArg G.hubLabel hhk), hlabels⟩

include H in
theorem rims_facial_covers (a : G.SunRimDart hn) :
    (∃ side, (G.sunRimSimpleCircuit hn (by simp) hw a).BoundsFaceOrbit side) ∧
      (G.sunRimSimpleCircuit hn (by simp) hw a).IsLabelCover :=
  ⟨H.faces a, H.rim_isLabelCover hn hw a⟩

end SunFaceState
end ThomGame.Pictures.PortGraph
