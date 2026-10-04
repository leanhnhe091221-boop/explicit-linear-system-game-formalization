module

public import ThomGame.Construction.WheelOddIndependentRim

/-!
# Actual edge deletion for a pure-independent exceptional rim

Delete slot 2 at every selected hub, retain slot 1 and its actual
partner, and give that edge the external slot-0 label. Each selected
hub becomes a two-port joint. All other hubs and ports are unchanged.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures PortGraph
open scoped Classical BigOperators

variable {H : SigmaGraph [] []} [IsEmpty H.Joint]
  (a : H.RimDart (numberedWheelCycles oddWheelCycle)) (hi : OddRimIndependentOnly H a)

noncomputable def oddIndependentRetainedPort (i : Fin (closedSigmaRimCircuit H oddWheelCycle a).length) : H.Dart :=
  .hub ((closedSigmaRimCircuit H oddWheelCycle a).hubAt i) (1 : Fin 3)

def OddIndependentCutKeep (x : H.Dart) : Prop :=
  ¬ (closedSigmaRimCircuit H oddWheelCycle a).Marked x ∨ x ∈ Set.range (oddIndependentRetainedPort a)

include hi in
theorem oddIndependentCutKeep_twin (x : H.Dart) :
    OddIndependentCutKeep a (H.pairing.twin x) ↔ OddIndependentCutKeep a x := by
  have ht (y : H.Dart) (hy : OddIndependentCutKeep a y) :
      OddIndependentCutKeep a (H.pairing.twin y) := by
    rcases hy with hy | ⟨i, rfl⟩
    · exact Or.inl (fun hm => hy (((closedSigmaRimCircuit H oddWheelCycle a).marked_twin_iff y).mp hm))
    · exact Or.inr ⟨oddIndependentPartner a hi i, (oddIndependentPartner_paired a hi i).symm⟩
  exact ⟨fun hx => H.pairing.involutive x ▸ ht _ hx, ht x⟩

noncomputable def oddIndependentCutLabel (x : H.Dart) : Fin 1889684 :=
  if x ∈ Set.range (oddIndependentRetainedPort a) then
    numberedSystem.column (rowEquiv oddRow) 0
  else Port.label H.jointLabel x

theorem oddIndependentCutLabel_retained (i : Fin (closedSigmaRimCircuit H oddWheelCycle a).length) :
    oddIndependentCutLabel a (oddIndependentRetainedPort a i) =
      numberedSystem.column (rowEquiv oddRow) 0 :=
  ite_eq_left ⟨i, rfl⟩

include hi in
theorem oddIndependentCutLabel_unmarked (x : H.Dart) (hx : ¬ (closedSigmaRimCircuit H oddWheelCycle a).Marked x) :
    oddIndependentCutLabel a x = Port.label H.jointLabel x := by
  apply ite_eq_right
  rintro ⟨i, rfl⟩
  exact hx ((oddIndependent_hub_port_marked a hi i 1).mpr (by decide +kernel))

include hi in
theorem oddIndependentCutLabel_twin (x : H.Dart) (hx : OddIndependentCutKeep a x) :
    oddIndependentCutLabel a (H.pairing.twin x) = oddIndependentCutLabel a x := by
  rcases hx with hx | ⟨i, rfl⟩
  · rw [oddIndependentCutLabel_unmarked a hi x hx,
      oddIndependentCutLabel_unmarked a hi _ (fun hm => hx (((closedSigmaRimCircuit H oddWheelCycle a).marked_twin_iff x).mp hm)),
      H.pairing.label_twin]
  · change oddIndependentCutLabel a (H.pairing.twin (.hub ((closedSigmaRimCircuit H oddWheelCycle a).hubAt i) (1 : Fin 3))) = _
    rw [oddIndependentPartner_paired a hi i]
    exact (oddIndependentCutLabel_retained a _).trans (oddIndependentCutLabel_retained a i).symm

noncomputable def oddIndependentCutPairing :
    Pairing (fun x : Subtype (OddIndependentCutKeep a) => oddIndependentCutLabel a x.val) where
  twin x := ⟨H.pairing.twin x.val, (oddIndependentCutKeep_twin a hi x.val).mpr x.property⟩
  involutive x := Subtype.ext (H.pairing.involutive x.val)
  ne_self x hx := H.pairing.ne_self x.val (congrArg Subtype.val hx)
  label_twin x := oddIndependentCutLabel_twin a hi x.val x.property

include hi in
theorem oddIndependentCutKeep_hubAt (i : Fin (closedSigmaRimCircuit H oddWheelCycle a).length) (p : Fin 3) :
    OddIndependentCutKeep a (.hub ((closedSigmaRimCircuit H oddWheelCycle a).hubAt i) p) ↔ p = 0 ∨ p = 1 := by
  constructor
  · rintro (hx | ⟨j, hj⟩)
    · exact Or.inl (not_not.mp (fun hp => hx ((oddIndependent_hub_port_marked a hi i p).mpr hp)))
    · exact Or.inr (H.row_hub_eq_iff.mp hj).2.symm
  · rintro (rfl | rfl)
    · exact Or.inl (fun hm => (oddIndependent_hub_port_marked a hi i 0).mp hm rfl)
    · exact Or.inr ⟨i, rfl⟩

abbrev OddIndependentCutDart := Port (SolutionGroup.triangularPresentation numberedSystem) [] [] (closedSigmaRimCircuit H oddWheelCycle a).ErasedCircuitHub
  (Fin (closedSigmaRimCircuit H oddWheelCycle a).length) (fun h => H.hubLabel h.val)

noncomputable def oddIndependentCutPort : OddIndependentCutDart a → H.Dart
  | .top j => .top j
  | .bottom j => .bottom j
  | .hub h p => .hub h.val p
  | .joint i false => .hub ((closedSigmaRimCircuit H oddWheelCycle a).hubAt i) (1 : Fin 3)
  | .joint i true => .hub ((closedSigmaRimCircuit H oddWheelCycle a).hubAt i) (0 : Fin 3)

theorem oddIndependentCutPort_hub_unmarked (h : (closedSigmaRimCircuit H oddWheelCycle a).ErasedCircuitHub) (p : Fin 3) :
    ¬ (closedSigmaRimCircuit H oddWheelCycle a).Marked (.hub h.val p) := by
  rintro ⟨⟨i, side⟩, he⟩
  obtain ⟨q, hq⟩ := (closedSigmaRimCircuit H oddWheelCycle a).port_eq_hubAt i side
  exact h.property ⟨i, (H.row_hub_eq_iff.mp (hq.symm.trans he)).1⟩

include hi in
theorem oddIndependentCutPort_kept (x : OddIndependentCutDart a) :
    OddIndependentCutKeep a (oddIndependentCutPort a x) := by
  cases x with
  | top j => exact j.elim0
  | bottom j => exact j.elim0
  | hub h p => exact Or.inl (oddIndependentCutPort_hub_unmarked a h p)
  | joint i side =>
    cases side
    · exact Or.inr ⟨i, rfl⟩
    · exact (oddIndependentCutKeep_hubAt a hi i 0).mpr (Or.inl rfl)

theorem oddIndependentCutPort_injective : Function.Injective (oddIndependentCutPort a) := by
  intro x y he
  cases x with
  | top j => exact j.elim0
  | bottom j => exact j.elim0
  | hub h p =>
    cases y with
    | top j => exact j.elim0
    | bottom j => exact j.elim0
    | hub k q =>
      obtain ⟨hh, hp⟩ := H.row_hub_eq_iff.mp he
      have hh' : h = k := Subtype.ext hh
      subst k
      exact congrArg (Port.hub h) hp
    | joint i side =>
      cases side <;> exact (h.property ⟨i, (H.row_hub_eq_iff.mp he).1.symm⟩).elim
  | joint i side =>
    cases y with
    | top j => exact j.elim0
    | bottom j => exact j.elim0
    | hub h p =>
      cases side <;> exact (h.property ⟨i, (H.row_hub_eq_iff.mp he).1⟩).elim
    | joint j t =>
      cases side <;> cases t
      · exact congrArg (fun k => (Port.joint k false : OddIndependentCutDart a))
          ((closedSigmaRimCircuit H oddWheelCycle a).hubAt_injective (H.row_hub_eq_iff.mp he).1)
      · exact (show (1 : Fin 3) ≠ 0 by decide +kernel) (H.row_hub_eq_iff.mp he).2 |>.elim
      · exact (show (0 : Fin 3) ≠ 1 by decide +kernel) (H.row_hub_eq_iff.mp he).2 |>.elim
      · exact congrArg (fun k => (Port.joint k true : OddIndependentCutDart a))
          ((closedSigmaRimCircuit H oddWheelCycle a).hubAt_injective (H.row_hub_eq_iff.mp he).1)

include hi in
theorem oddIndependentCutPort_surjective (x : H.Dart) (hx : OddIndependentCutKeep a x) :
    ∃ y : OddIndependentCutDart a, oddIndependentCutPort a y = x := by
  cases x with
  | top j => exact j.elim0
  | bottom j => exact j.elim0
  | joint j side => exact isEmptyElim j
  | hub h p =>
    by_cases hh : h ∈ Set.range (closedSigmaRimCircuit H oddWheelCycle a).hubAt
    · obtain ⟨i, rfl⟩ := hh
      rcases (oddIndependentCutKeep_hubAt a hi i p).mp hx with rfl | rfl
      · exact ⟨.joint i true, rfl⟩
      · exact ⟨.joint i false, rfl⟩
    · exact ⟨.hub ⟨h, hh⟩ p, rfl⟩

noncomputable def oddIndependentCutPorts :
    OddIndependentCutDart a ≃ Subtype (OddIndependentCutKeep a) :=
  Equiv.ofBijective (fun x => ⟨oddIndependentCutPort a x, oddIndependentCutPort_kept a hi x⟩)
    ⟨fun _ _ h => oddIndependentCutPort_injective a (congrArg Subtype.val h), by
      rintro ⟨x, hx⟩
      obtain ⟨y, hy⟩ := oddIndependentCutPort_surjective a hi x hx
      exact ⟨y, Subtype.ext hy⟩⟩

noncomputable def oddIndependentCutJointLabel (_ : Fin (closedSigmaRimCircuit H oddWheelCycle a).length) : Fin 1889684 :=
  numberedSystem.column (rowEquiv oddRow) 0

include hi in
theorem oddIndependentCutPort_label (x : OddIndependentCutDart a) :
    oddIndependentCutLabel a (oddIndependentCutPort a x) =
      Port.label (oddIndependentCutJointLabel a) x := by
  cases x with
  | top j => exact j.elim0
  | bottom j => exact j.elim0
  | hub h p => exact oddIndependentCutLabel_unmarked a hi _ (oddIndependentCutPort_hub_unmarked a h p)
  | joint i side =>
    cases side
    · exact oddIndependentCutLabel_retained a i
    · exact (oddIndependentCutLabel_unmarked a hi _
        (fun hm => (oddIndependent_hub_port_marked a hi i 0).mp hm rfl)).trans
          (oddIndependent_hub_port_label a hi i 0)

@[reducible] noncomputable def oddIndependentCutGraph : SigmaGraph [] [] where
  Hub := (closedSigmaRimCircuit H oddWheelCycle a).ErasedCircuitHub
  Joint := Fin (closedSigmaRimCircuit H oddWheelCycle a).length
  hubLabel h := H.hubLabel h.val
  hubFlip h := H.hubFlip h.val
  jointLabel := oddIndependentCutJointLabel a
  pairing := (oddIndependentCutPairing a hi).transport (oddIndependentCutPorts a hi).symm _ (by
    intro x
    obtain ⟨y, rfl⟩ := (oddIndependentCutPorts a hi).surjective x
    rw [Equiv.symm_apply_apply]
    exact (oddIndependentCutPort_label a hi y).symm)

theorem oddIndependentCutGraph_twin (x : (oddIndependentCutGraph a hi).Dart) :
    oddIndependentCutPort a ((oddIndependentCutGraph a hi).pairing.twin x) =
      H.pairing.twin (oddIndependentCutPort a x) :=
  congrArg Subtype.val ((oddIndependentCutPorts a hi).apply_symm_apply
    ((oddIndependentCutPairing a hi).twin (oddIndependentCutPorts a hi x)))

theorem oddIndependentCutGraph_character : (oddIndependentCutGraph a hi).character = H.character := by
  funext r
  rw [PortGraph.character_eq_sum, H.character_eq_sum]
  exact oddIndependent_erased_weight a hi (fun j => if j = r then 1 else 0)

theorem oddIndependentCutGraph_sign : (oddIndependentCutGraph a hi).sign = H.sign :=
  sign_eq_of_character (oddIndependentCutGraph_character a hi)

theorem oddIndependentCutGraph_hub_card :
    Fintype.card (oddIndependentCutGraph a hi).Hub + (closedSigmaRimCircuit H oddWheelCycle a).length = Fintype.card H.Hub :=
  (closedSigmaRimCircuit H oddWheelCycle a).erasedCircuitHub_card

theorem oddIndependentCutGraph_hub_card_lt :
    Fintype.card (oddIndependentCutGraph a hi).Hub < Fintype.card H.Hub :=
  (closedSigmaRimCircuit H oddWheelCycle a).erasedCircuitHub_card_lt

end ThomGame.Construction
