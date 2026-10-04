module

public import ThomGame.Pictures.SunBandMatching

/-!
# The matching of the remaining ports at a three-label sun circuit

Each circuit vertex has exactly one unused rim port. Its slot depends
only on the hub label, so the actual spoke matching pairs equal labels
on these remaining ports. This specifies the reconnection in the
cycle-erasure argument without assuming that the erasure is planar.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) u v} [IsEmpty G.Joint]
  (C : G.SimpleCircuit) (hn : 3 ≤ n) (i : Fin n)
  (hband : ∀ k : Fin C.length, SunBandLabel i (Port.label G.jointLabel (C.dart k)))

include hn hband in
theorem sunBand_hub_labels (k : Fin C.length) :
    G.hubLabel (C.hubAt k) = i ∨ G.hubLabel (C.hubAt k) = (finRotate n).symm i := by
  obtain ⟨⟨l, side⟩, hl⟩ := C.sunBand_spoke_marked hn i hband k
  have hb := C.sunBand_port_label i hband l side
  rw [hl] at hb
  change SunBandLabel i (Sum.inl (G.hubLabel (C.hubAt k))) at hb
  simpa only [SunBandLabel, Sum.inl_ne_inr, Sum.inl.injEq, false_or] using hb

noncomputable def sunBandExternalSlot (k : Fin C.length) : Fin 3 :=
  if G.hubLabel (C.hubAt k) = i then 2 else 1

noncomputable def sunBandExternalPort (k : Fin C.length) : G.Dart :=
  .hub (C.hubAt k) (C.sunBandExternalSlot i k)

theorem sunBandExternalPort_vertex (k : Fin C.length) :
    (C.sunBandExternalPort i k).vertex = (C.dart k).vertex := (C.hubAt_vertex k).symm

theorem sunBandExternalPort_injective : Function.Injective (C.sunBandExternalPort i) := by
  intro j k he
  exact C.vertex_injective ((C.sunBandExternalPort_vertex i j).symm.trans
    ((congrArg Port.vertex he).trans (C.sunBandExternalPort_vertex i k)))

include hn in
theorem sunBandExternalPort_label_not_band (k : Fin C.length) :
    ¬ SunBandLabel i (Port.label G.jointLabel (C.sunBandExternalPort i k)) := by
  intro ha
  by_cases hk : G.hubLabel (C.hubAt k) = i
  · have hs : C.sunBandExternalSlot i k = 2 := ite_eq_left hk
    have hl : Port.label G.jointLabel (C.sunBandExternalPort i k) =
        Sum.inr (finRotate n (G.hubLabel (C.hubAt k))) :=
      congrArg (fun p : Fin 3 => Port.label G.jointLabel (.hub (C.hubAt k) p : G.Dart)) hs
    have he := (sunBandLabel_rim i (finRotate n (G.hubLabel (C.hubAt k)))).mp (hl ▸ ha)
    exact Hypergraph.sun_next_ne_self hn i ((congrArg (finRotate n) hk).symm.trans he)
  · have hs : C.sunBandExternalSlot i k = 1 := ite_eq_right hk
    have hl : Port.label G.jointLabel (C.sunBandExternalPort i k) = Sum.inr (G.hubLabel (C.hubAt k)) :=
      congrArg (fun p : Fin 3 => Port.label G.jointLabel (.hub (C.hubAt k) p : G.Dart)) hs
    exact hk ((sunBandLabel_rim i (G.hubLabel (C.hubAt k))).mp (hl ▸ ha))

include hn hband in
theorem sunBandExternalPort_unmarked (k : Fin C.length) : ¬ C.Marked (C.sunBandExternalPort i k) := by
  rintro ⟨⟨l, side⟩, hl⟩
  exact C.sunBandExternalPort_label_not_band hn i k
    (hl ▸ C.sunBand_port_label i hband l side)

theorem sunBandExternalSlot_partner (k : Fin C.length) :
    C.sunBandExternalSlot i (C.sunBandPartner hn i hband k) = C.sunBandExternalSlot i k := by
  unfold sunBandExternalSlot
  rw [C.sunBandPartner_label hn i hband k]

theorem sunBandExternalPort_partner_label (k : Fin C.length) :
    Port.label G.jointLabel (C.sunBandExternalPort i (C.sunBandPartner hn i hband k)) =
      Port.label G.jointLabel (C.sunBandExternalPort i k) := by
  unfold sunBandExternalPort
  rw [C.sunBandExternalSlot_partner hn i hband k]
  exact G.sun_same_hubLabel_port_label (C.sunBandPartner_label hn i hband k) _

noncomputable def sunBandExternalPairing :
    Pairing (fun k : Fin C.length => Port.label G.jointLabel (C.sunBandExternalPort i k)) where
  twin := C.sunBandPartner hn i hband
  involutive := C.sunBandPartner_involutive hn i hband
  ne_self := C.sunBandPartner_ne_self hn i hband
  label_twin := C.sunBandExternalPort_partner_label hn i hband

include hn hband in
theorem sunBandExternalPort_unique (k : Fin C.length) (x : G.Dart)
    (hv : x.vertex = (C.dart k).vertex) (hx : ¬ C.Marked x) :
    x = C.sunBandExternalPort i k := by
  have hvh := hv.trans (C.hubAt_vertex k)
  cases x with
  | top j => cases hvh
  | bottom j => cases hvh
  | joint j side => exact isEmptyElim j
  | hub h t =>
    have hh : h = C.hubAt k := Sum.inl.inj (Sum.inr.inj hvh)
    subst h
    obtain ⟨p, hp⟩ := C.port_eq_hubAt k false
    obtain ⟨q, hq⟩ := C.port_eq_hubAt k true
    have hpq : p ≠ q := by
      intro he
      exact C.incoming_ne_outgoing k (hq.trans ((congrArg (Port.hub (C.hubAt k)) he.symm).trans hp.symm))
    have htP : t ≠ p := fun he => hx ⟨(k, false), hp.trans (congrArg (Port.hub (C.hubAt k)) he.symm)⟩
    have htQ : t ≠ q := fun he => hx ⟨(k, true), hq.trans (congrArg (Port.hub (C.hubAt k)) he.symm)⟩
    have hP : C.sunBandExternalSlot i k ≠ p := by
      intro he
      exact C.sunBandExternalPort_unmarked hn i hband k
        ⟨(k, false), hp.trans (congrArg (Port.hub (C.hubAt k)) he.symm)⟩
    have hQ : C.sunBandExternalSlot i k ≠ q := by
      intro he
      exact C.sunBandExternalPort_unmarked hn i hband k
        ⟨(k, true), hq.trans (congrArg (Port.hub (C.hubAt k)) he.symm)⟩
    have he : t = C.sunBandExternalSlot i k := by
      have hp3 : p.val < 3 := p.isLt
      have hq3 : q.val < 3 := q.isLt
      have ht3 : t.val < 3 := t.isLt
      have hr3 : (C.sunBandExternalSlot i k).val < 3 := (C.sunBandExternalSlot i k).isLt
      omega
    exact congrArg (Port.hub (C.hubAt k)) he

include hn hband in
theorem sunBandExternalPort_complete (x : G.Dart)
    (hv : ∃ k, (C.dart k).vertex = x.vertex) (hx : ¬ C.Marked x) :
    ∃! k : Fin C.length, C.sunBandExternalPort i k = x := by
  obtain ⟨k, hk⟩ := hv
  have he := (C.sunBandExternalPort_unique hn i hband k x hk.symm hx).symm
  exact ⟨k, he, fun l hl => C.sunBandExternalPort_injective i (hl.trans he.symm)⟩

end ThomGame.Pictures.PortGraph.SimpleCircuit
