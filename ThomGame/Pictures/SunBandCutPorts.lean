module

public import ThomGame.Pictures.SunBandCutLabels

/-!
# Ports after deleting the fixed rim edges of a three-label circuit

Each selected hub becomes a joint whose two ports are the original
spoke and the unused rim port. The resulting ports are exactly the
retained subset; boundary positions and all other hubs are unchanged.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open scoped Classical

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) u v} [IsEmpty G.Joint]
  (C : G.SimpleCircuit) (hn : 3 ≤ n) (i : Fin n)
  (hband : ∀ k : Fin C.length, SunBandLabel i (Port.label G.jointLabel (C.dart k)))

theorem sunBandExternalSlot_ne_zero (k : Fin C.length) : C.sunBandExternalSlot i k ≠ 0 := by
  unfold sunBandExternalSlot
  split <;> decide +kernel

include hn hband in
theorem sunBandCutKeep_hubAt_iff (k : Fin C.length) (p : Fin 3) :
    C.SunBandCutKeep (.hub (C.hubAt k) p) ↔ p = 0 ∨ p = C.sunBandExternalSlot i k := by
  constructor
  · rintro (hx | ⟨l, hl⟩)
    · have he := C.sunBandExternalPort_unique hn i hband k (.hub (C.hubAt k) p)
        (C.hubAt_vertex k).symm hx
      exact Or.inr (G.sun_hub_eq_iff.mp he).2
    · exact Or.inl (G.sun_hub_eq_iff.mp hl).2.symm
  · rintro (rfl | rfl)
    · exact Or.inr ⟨k, rfl⟩
    · exact Or.inl (C.sunBandExternalPort_unmarked hn i hband k)

abbrev SunBandCutDart := Port (sunPresentation n b) u v C.ErasedCircuitHub
  (Fin C.length) (fun h => G.hubLabel h.val)

noncomputable def sunBandCutPort : C.SunBandCutDart → G.Dart
  | .top j => .top j
  | .bottom j => .bottom j
  | .hub h p => .hub h.val p
  | .joint k false => C.sunBandSpokePort k
  | .joint k true => C.sunBandExternalPort i k

include hn hband in
theorem sunBandCutPort_kept (x : C.SunBandCutDart) : C.SunBandCutKeep (C.sunBandCutPort i x) := by
  cases x with
  | top j =>
    apply Or.inl
    rintro ⟨⟨k, side⟩, he⟩
    obtain ⟨p, hp⟩ := C.port_eq_hubAt k side
    cases hp.symm.trans he
  | bottom j =>
    apply Or.inl
    rintro ⟨⟨k, side⟩, he⟩
    obtain ⟨p, hp⟩ := C.port_eq_hubAt k side
    cases hp.symm.trans he
  | hub h p =>
    apply Or.inl
    rintro ⟨⟨k, side⟩, he⟩
    obtain ⟨q, hq⟩ := C.port_eq_hubAt k side
    exact h.property ⟨k, (G.sun_hub_eq_iff.mp (hq.symm.trans he)).1⟩
  | joint k side =>
    cases side
    · exact Or.inr ⟨k, rfl⟩
    · exact Or.inl (C.sunBandExternalPort_unmarked hn i hband k)

theorem sunBandCutPort_injective : Function.Injective (C.sunBandCutPort i) := by
  intro x y he
  cases x with
  | top j =>
    cases y with
    | top k => exact congrArg Port.top (Port.top.inj he)
    | bottom k => cases he
    | hub h p => cases he
    | joint k side => cases side <;> cases he
  | bottom j =>
    cases y with
    | top k => cases he
    | bottom k => exact congrArg Port.bottom (Port.bottom.inj he)
    | hub h p => cases he
    | joint k side => cases side <;> cases he
  | hub h p =>
    cases y with
    | top k => cases he
    | bottom k => cases he
    | hub k q =>
      obtain ⟨hh, hp⟩ := G.sun_hub_eq_iff.mp he
      have hh' : h = k := Subtype.ext hh
      subst k
      exact congrArg (Port.hub h) hp
    | joint k side =>
      cases side <;> exact (h.property ⟨k, (G.sun_hub_eq_iff.mp he).1.symm⟩).elim
  | joint k side =>
    cases y with
    | top j => cases side <;> cases he
    | bottom j => cases side <;> cases he
    | hub h p =>
      cases side <;> exact (h.property ⟨k, (G.sun_hub_eq_iff.mp he).1⟩).elim
    | joint l t =>
      cases side <;> cases t
      · exact congrArg (fun k => (Port.joint k false : C.SunBandCutDart))
          (C.sunBandSpokePort_injective he)
      · exact (C.sunBandExternalSlot_ne_zero i l (G.sun_hub_eq_iff.mp he).2.symm).elim
      · exact (C.sunBandExternalSlot_ne_zero i k (G.sun_hub_eq_iff.mp he).2).elim
      · exact congrArg (fun k => (Port.joint k true : C.SunBandCutDart))
          (C.sunBandExternalPort_injective i he)

include hn hband in
theorem sunBandCutPort_surjective (x : G.Dart) (hx : C.SunBandCutKeep x) :
    ∃ y : C.SunBandCutDart, C.sunBandCutPort i y = x := by
  rcases hx with hx | ⟨k, rfl⟩
  · cases x with
    | top j => exact ⟨.top j, rfl⟩
    | bottom j => exact ⟨.bottom j, rfl⟩
    | joint j side => exact isEmptyElim j
    | hub h p =>
      by_cases hh : h ∈ Set.range C.hubAt
      · obtain ⟨k, hk⟩ := hh
        have hv : (Port.hub h p : G.Dart).vertex = (C.dart k).vertex := by
          rw [C.hubAt_vertex, hk]
          rfl
        exact ⟨.joint k true, (C.sunBandExternalPort_unique hn i hband k (.hub h p) hv hx).symm⟩
      · exact ⟨.hub ⟨h, hh⟩ p, rfl⟩
  · exact ⟨.joint k false, rfl⟩

noncomputable def sunBandCutPorts : C.SunBandCutDart ≃ Subtype C.SunBandCutKeep :=
  Equiv.ofBijective (fun x => ⟨C.sunBandCutPort i x, C.sunBandCutPort_kept hn i hband x⟩)
    ⟨fun _ _ h => C.sunBandCutPort_injective i (congrArg Subtype.val h), by
      rintro ⟨x, hx⟩
      obtain ⟨y, hy⟩ := C.sunBandCutPort_surjective hn i hband x hx
      exact ⟨y, Subtype.ext hy⟩⟩

noncomputable def sunBandCutJointLabel (k : Fin C.length) : Fin n ⊕ Fin n :=
  Port.label G.jointLabel (C.sunBandExternalPort i k)

include hn hband in
theorem sunBandCutPort_label (x : C.SunBandCutDart) :
    C.sunBandCutLabel i (C.sunBandCutPort i x) = Port.label (C.sunBandCutJointLabel i) x := by
  cases x with
  | top j =>
    apply C.sunBandCutLabel_unmarked hn i hband
    rintro ⟨⟨k, side⟩, he⟩
    obtain ⟨p, hp⟩ := C.port_eq_hubAt k side
    cases hp.symm.trans he
  | bottom j =>
    apply C.sunBandCutLabel_unmarked hn i hband
    rintro ⟨⟨k, side⟩, he⟩
    obtain ⟨p, hp⟩ := C.port_eq_hubAt k side
    cases hp.symm.trans he
  | hub h p =>
    apply C.sunBandCutLabel_unmarked hn i hband
    rintro ⟨⟨k, side⟩, he⟩
    obtain ⟨q, hq⟩ := C.port_eq_hubAt k side
    exact h.property ⟨k, (G.sun_hub_eq_iff.mp (hq.symm.trans he)).1⟩
  | joint k side =>
    cases side
    · exact C.sunBandCutLabel_spoke i k
    · exact C.sunBandCutLabel_unmarked hn i hband _ (C.sunBandExternalPort_unmarked hn i hband k)

end ThomGame.Pictures.PortGraph.SimpleCircuit
