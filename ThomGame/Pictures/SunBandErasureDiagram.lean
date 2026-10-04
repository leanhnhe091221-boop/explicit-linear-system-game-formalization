module

public import ThomGame.Pictures.SunBandCutReturn
public import ThomGame.Pictures.SunMinimalState
public import ThomGame.Pictures.BoundaryCircuitTransport

/-!
# Genuine smaller diagrams after erasing a three-label sun circuit

Edge deletion preserves capped Euler saturation through the first-return
rotation. Realizing this actual graph and puncturing its boundary cap
gives the prescribed boundary word, with exactly the circuit's hubs
removed. Boundary reversal gives the lower-boundary version as well.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open Equiv RibbonConnectivity
open scoped Classical BigOperators

variable {n : Nat} {b : Fin n → ZMod 2} {w : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) w []} [IsEmpty G.Joint]
  (C : G.SimpleCircuit) (hn : 3 ≤ n) (i : Fin n)
  (hband : ∀ k : Fin C.length, SunBandLabel i (Port.label G.jointLabel (C.dart k)))

theorem sunBandCutGraph_capped_saturated
    (hcap : RotationEuler.count G.cappedRotation G.pairing.perm =
      2 * Nat.card (Component G.cappedRotation G.pairing.perm)) :
    RotationEuler.count (C.sunBandCutGraph hn i hband).cappedRotation
        (C.sunBandCutGraph hn i hband).pairing.perm =
      2 * Nat.card (Component (C.sunBandCutGraph hn i hband).cappedRotation
        (C.sunBandCutGraph hn i hband).pairing.perm) := by
  let H := C.sunBandCutGraph hn i hband
  let r := MarkedReturn.perm G.cappedRotation C.SunBandCutKeep
  let t := G.pairing.perm.subtypePerm (C.sunBandCutKeep_twin hn i hband)
  let e := C.sunBandCutPorts hn i hband
  have hr : ∀ x, r (e x) = e (H.cappedRotation x) := C.sunBandCutGraph_cappedRotation hn i hband
  have ht : ∀ x, t (e x) = e (H.pairing.perm x) :=
    fun x => Subtype.ext (C.sunBandCutGraph_twin hn i hband x).symm
  rw [RotationEuler.count_congr H.cappedRotation H.pairing.perm r t e hr ht,
    Nat.card_congr (componentCongrEquiv H.cappedRotation H.pairing.perm r t e hr ht)]
  exact RotationEuler.firstReturnRotation_saturated G.cappedRotation C.SunBandCutKeep
    G.pairing.perm (C.sunBandCutKeep_twin hn i hband) G.pairing.involutive hcap

include hn hband in
theorem exists_sunBand_erased_top_diagram (hw : 0 < w.length)
    (hEuler : eulerDefect G.pairing.perm G.circuitStep = 0)
    (hnc : G.BoundaryNoncrossing) (hsees : G.BoundarySeesComponents) :
    ∃ d : Diagram (sunPresentation n b) w [],
      (d.labels : Multiset (Fin n)) + (∑ k : Fin C.length, ([G.hubLabel (C.hubAt k)] : Multiset (Fin n))) =
        (∑ h : G.Hub, ([G.hubLabel h] : Multiset (Fin n))) ∧
      d.size + C.length = Fintype.card G.Hub ∧ d.sign = G.sign ∧
      (∀ j, d.character j = G.character j) := by
  have hpos (h : G.Hub) : 0 < ((sunPresentation n b).word (G.hubLabel h)).length := by
    change 0 < 3
    decide +kernel
  have hcap := C.sunBandCutGraph_capped_saturated hn i hband
    (G.cappedRotation_saturated_general hw hpos hEuler hnc hsees)
  obtain ⟨d, hd, hc, hs⟩ := (C.sunBandCutGraph hn i hband).exists_diagram_of_capped_saturated_preserving
    hw (fun _ => by change 0 < 3; decide +kernel) hcap
  refine ⟨d, ?_, ?_, hs.trans (C.sunBandCutGraph_sign hn i hband), ?_⟩
  · rw [hd]
    exact C.sunBandCutGraph_relations hn i hband
  · rw [hc]
    exact C.sunBandCutGraph_hub_card hn i hband
  · intro j
    rw [d.sun_character, G.sun_character]

variable {B : PortGraph (sunPresentation n b) [] w} [IsEmpty B.Joint]
  (D : B.SimpleCircuit)
  (hD : ∀ k : Fin D.length, SunBandLabel i (Port.label B.jointLabel (D.dart k)))

include hn hD in
theorem exists_sunBand_erased_bottom_diagram (hw : 0 < w.length)
    (hEuler : eulerDefect B.pairing.perm B.circuitStep = 0)
    (hnc : B.BoundaryNoncrossing) (hsees : B.BoundarySeesComponents) :
    ∃ d : Diagram (sunPresentation n b) [] w,
      d.size + D.length = Fintype.card B.Hub ∧ d.sign = B.sign ∧
      (∀ j, d.character j = B.character j) := by
  have hband' (k : Fin D.bottomTopCircuit.length) :
      SunBandLabel i (Port.label B.bottomTopGraph.jointLabel (D.bottomTopCircuit.dart k)) := by
    change SunBandLabel i (Port.label B.jointLabel (B.bottomTopPorts (D.dart k)))
    rw [B.bottomTopPorts_label]
    exact hD k
  obtain ⟨d, _, hc, _, _⟩ := D.bottomTopCircuit.exists_sunBand_erased_top_diagram hn i hband'
    (by simpa only [List.length_reverse] using hw) (B.bottomTop_eulerDefect.trans hEuler)
    (B.bottomTop_boundaryNoncrossing hnc) (B.bottomTop_boundarySeesComponents hsees)
  refine ⟨d.fromReversedTop, ?_, ?_, ?_⟩
  · rw [d.size_fromReversedTop]
    exact hc
  · rw [d.fromReversedTop.sign_eq_character, B.sign_eq_character]
    simp_rw [d.fromReversedTop.sun_character, B.sun_character]
  · intro j
    rw [d.fromReversedTop.sun_character, B.sun_character]

end ThomGame.Pictures.PortGraph.SimpleCircuit
