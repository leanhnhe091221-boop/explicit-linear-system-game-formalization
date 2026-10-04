module

public import ThomGame.Pictures.SunSwitchTermination

/-!
# Termination for actual fully smoothed character-minimal sun diagrams

The original diagram supplies minimality and all boundary witnesses.
The output is a genuine finite trace of inward switches, has no remaining
inward spoke at any rim hub, and preserves size, sign, and the specified
boundary. Smoothing's circle list remains an explicit input; it is not
silently absorbed into the port-graph count.
-/

@[expose] public section
namespace ThomGame.Pictures

open RibbonConnectivity
open scoped BigOperators

namespace Diagram

theorem graph_hub_relations {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
    (d : Diagram P u v) :
    (∑ h : d.graph.Hub, ([d.graph.hubLabel h] : Multiset R)) = (d.labels : Multiset R) := by
  simp_rw [d.hubLabel_index]
  change (∑ h, (fun i : Fin d.labels.length => ([d.labels[i]] : Multiset R)) (d.hubIndex h)) = _
  rw [d.hubIndex.sum_comp (fun i : Fin d.labels.length => ([d.labels[i]] : Multiset R))]
  change (∑ i : Fin d.labels.length, ([d.labels[i.val]] : Multiset R)) = _
  rw [Fin.sum_univ_fun_getElem d.labels (fun r : R => ([r] : Multiset R))]
  exact Multiset.sum_map_singleton (d.labels : Multiset R)

end Diagram

variable {n : Nat} {b : Fin n → ZMod 2} {w : List (Fin n ⊕ Fin n)}

namespace PortGraph

variable {G : PortGraph (sunPresentation n b) [] w} [IsEmpty G.Joint]
  (hn : 3 ≤ n) (hw : ∀ z ∈ w, ∃ j, z = Sum.inl j)

theorem noInteriorSunSpoke_hub (hNo : G.NoInteriorSunSpoke hn hw) (h : G.Hub) :
    ¬ (G.sunRimSimpleCircuit hn (by simp) hw (G.sunRimPort hn h true)).CutInterior
      (.hub h (0 : Fin 3)) := by
  intro hi
  let C := G.sunRimSimpleCircuit hn (by simp) hw (G.sunRimPort hn h true)
  have he : Connected G.circuitStep C.cutPairing (.hub h (0 : Fin 3))
      (G.pairing.twin (.hub h (0 : Fin 3))) := by
    have hc := Connected.circuit (p := G.circuitStep) (f := C.cutPairing) (.hub h (0 : Fin 3))
    rw [C.cutPairing_of_unmarked _ (G.sunRimCircuit_spoke_unmarked hn (by simp) hw _ h)] at hc
    exact hc
  cases ht : G.pairing.twin (.hub h (0 : Fin 3)) with
  | top i => exact i.elim0
  | bottom i => exact hi.2 (.bottom i) trivial (ht ▸ he)
  | joint j side => exact isEmptyElim j
  | hub k p =>
    obtain ⟨_, hp, _⟩ := G.sun_spoke_hub_endpoints ht
    subst p
    exact hNo ⟨h, k, ht⟩ hi

theorem noInteriorSunSpoke_rim_hub (hNo : G.NoInteriorSunSpoke hn hw)
    (a : G.SunRimDart hn) (h : G.Hub)
    (hh : (G.sunRimSimpleCircuit hn (by simp) hw a).OnCircuitVertex (.inr (.inl h))) :
    ¬ (G.sunRimSimpleCircuit hn (by simp) hw a).CutInterior (.hub h (0 : Fin 3)) := by
  have hc := (G.sunRimCircuit_onHub_iff_connected hn (by simp) hw a h).mp hh
  have hm := G.sunRimCircuit_marked_iff_of_connected hn (by simp) hw a (G.sunRimPort hn h true) hc
  exact fun hi => G.noInteriorSunSpoke_hub hn hw hNo h
    (((G.sunRimSimpleCircuit hn (by simp) hw a).cutInterior_iff_of_marked
      (G.sunRimSimpleCircuit hn (by simp) hw (G.sunRimPort hn h true)) hm _).mp hi)

namespace SunSwitchTrace

theorem sign {G H : PortGraph (sunPresentation n b) [] w} (t : SunSwitchTrace G H) :
    H.sign = G.sign := by
  induction t with
  | refl _ => rfl
  | step _ _ ih => exact ih

end SunSwitchTrace
end PortGraph

namespace Smoothing

theorem exists_terminal_sun_switches {d : Diagram (sunPresentation n b) [] w}
    {G : PortGraph (sunPresentation n b) [] w} [IsEmpty G.Joint] {cs : List (Fin n ⊕ Fin n)}
    (t : Smoothing d.graph G cs) (hm : d.CharacterMinimal) (hn : 3 ≤ n)
    (hw : ∀ z ∈ w, ∃ j, z = Sum.inl j) :
    ∃ (H : PortGraph (sunPresentation n b) [] w) (q : PortGraph.SunSwitchTrace G H),
      q.Inward hn hw ∧ H.NoInteriorSunSpoke hn hw ∧ IsEmpty H.Joint ∧
      H.SunMinimalState ∧ H.HubsReachBoundary ∧
      Fintype.card H.Hub = d.size ∧ H.sign = d.sign ∧
      q.length ≤ G.sunTotalInteriorSpokeCount hn (by simp) hw
        (t.sunMinimalState hm).euler (t.sunMinimalState hm).sees
        (t.sun_rim_meetsBoundary hm hn (by simp) hw) := by
  have h := t.sunMinimalState hm
  have hb := t.sun_rim_meetsBoundary hm hn (by simp) hw
  obtain ⟨H, q, hq, hNo⟩ := h.exists_no_interior_spoke hn hw hb
  refine ⟨H, q, hq, hNo, q.isEmpty_joints inferInstance, q.minimalState h,
    q.hubsReachBoundary (t.sun_hubsReachBoundary hm),
    q.hub_card.trans (t.hub_card.trans d.graph_hub_card), q.sign.trans (t.sign.trans d.graph_sign), ?_⟩
  have hbound := q.inward_length_bound hn hw h hb hq
  omega

end Smoothing
end ThomGame.Pictures
