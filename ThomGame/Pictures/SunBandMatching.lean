module

public import ThomGame.Pictures.SunBandCircuit

/-! # The actual spoke matching on all vertices of a three-label sun circuit -/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) u v} [IsEmpty G.Joint]
  (C : G.SimpleCircuit) (hn : 3 ≤ n) (i : Fin n)
  (hband : ∀ k : Fin C.length, SunBandLabel i (Port.label G.jointLabel (C.dart k)))

include hn hband in
theorem sunBand_spoke_marked (k : Fin C.length) : C.Marked (.hub (C.hubAt k) (0 : Fin 3)) := by
  rcases C.sunBand_vertex_ports hn i hband k with ⟨hp, _⟩ | ⟨hp, _⟩
  · exact ⟨(k, false), hp⟩
  · exact ⟨(k, true), hp⟩

include hn hband in
theorem sunBand_spoke_partner (k : Fin C.length) :
    ∃! l : Fin C.length,
      G.pairing.twin (.hub (C.hubAt k) (0 : Fin 3)) = .hub (C.hubAt l) (0 : Fin 3) := by
  have hm := (C.marked_twin_iff (.hub (C.hubAt k) (0 : Fin 3))).mpr
    (C.sunBand_spoke_marked hn i hband k)
  obtain ⟨⟨l, side⟩, hl⟩ := hm
  obtain ⟨p, hp⟩ := C.port_eq_hubAt l side
  have he := hl.symm.trans hp
  obtain ⟨_, hp0, _⟩ := G.sun_spoke_hub_endpoints he
  have he0 : G.pairing.twin (.hub (C.hubAt k) (0 : Fin 3)) = .hub (C.hubAt l) (0 : Fin 3) :=
    he.trans (hp0 ▸ rfl)
  refine ⟨l, he0, ?_⟩
  intro j hj
  exact C.hubAt_injective (G.sun_hub_eq_iff.mp (hj.symm.trans he0)).1

noncomputable def sunBandPartner (k : Fin C.length) : Fin C.length :=
  (C.sunBand_spoke_partner hn i hband k).choose

theorem sunBandPartner_paired (k : Fin C.length) :
    G.pairing.twin (.hub (C.hubAt k) (0 : Fin 3)) =
      .hub (C.hubAt (C.sunBandPartner hn i hband k)) (0 : Fin 3) :=
  (C.sunBand_spoke_partner hn i hband k).choose_spec.1

theorem sunBandPartner_involutive : Function.Involutive (C.sunBandPartner hn i hband) := by
  intro k
  have he : (Port.hub (C.hubAt (C.sunBandPartner hn i hband (C.sunBandPartner hn i hband k)))
      (0 : Fin 3) : G.Dart) = .hub (C.hubAt k) (0 : Fin 3) :=
    (C.sunBandPartner_paired hn i hband (C.sunBandPartner hn i hband k)).symm.trans
    ((congrArg G.pairing.twin (C.sunBandPartner_paired hn i hband k).symm).trans
      (G.pairing.involutive (.hub (C.hubAt k) (0 : Fin 3))))
  exact C.hubAt_injective (G.sun_hub_eq_iff.mp he).1

theorem sunBandPartner_ne_self (k : Fin C.length) : C.sunBandPartner hn i hband k ≠ k := by
  intro he
  exact G.pairing.ne_self (.hub (C.hubAt k) (0 : Fin 3))
    ((C.sunBandPartner_paired hn i hband k).trans (congrArg (fun l => (Port.hub (C.hubAt l) (0 : Fin 3) : G.Dart)) he))

theorem sunBandPartner_label (k : Fin C.length) :
    G.hubLabel (C.hubAt (C.sunBandPartner hn i hband k)) = G.hubLabel (C.hubAt k) :=
  (G.sun_spoke_hub_endpoints (C.sunBandPartner_paired hn i hband k)).1

noncomputable def sunBandSpokePairing : Pairing (fun k : Fin C.length => G.hubLabel (C.hubAt k)) where
  twin := C.sunBandPartner hn i hband
  involutive := C.sunBandPartner_involutive hn i hband
  ne_self := C.sunBandPartner_ne_self hn i hband
  label_twin := C.sunBandPartner_label hn i hband

theorem sunBand_length_twice_pairs :
    C.length = 2 * Fintype.card (C.sunBandSpokePairing hn i hband).Edge := by
  simpa only [Fintype.card_fin] using (C.sunBandSpokePairing hn i hband).dart_card_eq_twice_edge_card

include hn hband in
theorem sunBand_length_even : Even C.length := by
  refine ⟨Fintype.card (C.sunBandSpokePairing hn i hband).Edge, ?_⟩
  simpa only [two_mul] using C.sunBand_length_twice_pairs hn i hband

end ThomGame.Pictures.PortGraph.SimpleCircuit
