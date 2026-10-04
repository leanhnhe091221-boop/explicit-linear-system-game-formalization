module

public import ThomGame.Construction.WheelRimCharacterMinimum
public import ThomGame.Pictures.SunBandErasureAccounting

/-!
# The actual pure-independent exceptional rims have paired odd-row hubs

The two labels meet only at the actual odd row. Both ports at every
circuit vertex therefore occupy row slots 1 and 2, and slot 0 is the
external spoke. Slot 1 pairs the circuit's distinct hubs, proving an
even length and zero contribution to every character coordinate.
-/

@[expose] public section
namespace ThomGame.Wheel.Family

variable {R V : Type*} [DecidableEq R] [DecidableEq V] (F : Family R V)

omit [DecidableEq R] [DecidableEq V] in
theorem pentagon_base_vertex (r : R) (j : Fin (F.size r)) :
    F.pentagonVertex r j 0 = ⟨r, j, 0⟩ := rfl

end ThomGame.Wheel.Family

namespace ThomGame.Construction

open Pictures PortGraph
open scoped Classical BigOperators

theorem numbered_pentagon_vertex (r : WheelIndex) (j : Fin (wheelFamily.size r)) (k : Fin 5) :
    (numberedWheelCycles (.inr ⟨r, j⟩)).vertex k =
      rowEquiv ((wheelCycles (.inr ⟨r, j⟩)).vertex k) := rfl

theorem odd_row_vertex_zero : (numberedWheelCycles oddWheelCycle).vertex 0 = rowEquiv oddRow :=
  (numbered_pentagon_vertex none 0 0).trans (congrArg rowEquiv (wheelFamily.pentagon_base_vertex none 0))

theorem odd_independent_edges_common_row (r : Fin 1417152)
    (h0 : (numberedWheelCycles oddWheelCycle).edge 0 ∈ numberedSystem.hypergraph.incidence r)
    (h1 : (numberedWheelCycles oddWheelCycle).edge 1 ∈ numberedSystem.hypergraph.incidence r) :
    r = rowEquiv oddRow := by
  rcases ((numberedWheelCycles oddWheelCycle).incident_iff r 0).mp h0 with he | he
  · exact he.trans odd_row_vertex_zero
  · rcases ((numberedWheelCycles oddWheelCycle).incident_iff r 1).mp h1 with hj | hj
    · have hi := (numberedWheelCycles oddWheelCycle).vertex.injective (he.symm.trans hj)
      exact (show (finRotate 5).symm (0 : Fin 5) ≠ 1 from by decide +kernel) hi |>.elim
    · have hp : (finRotate 5).symm (1 : Fin 5) = 0 := by decide +kernel
      exact hj.trans ((congrArg (numberedWheelCycles oddWheelCycle).vertex hp).trans odd_row_vertex_zero)

variable {H : SigmaGraph [] []} [IsEmpty H.Joint]
  (a : H.RimDart (numberedWheelCycles oddWheelCycle)) (hi : OddRimIndependentOnly H a)

include hi in
omit [IsEmpty H.Joint] in
theorem oddIndependent_marked_labels {x : H.Dart}
    (hx : (closedSigmaRimCircuit H oddWheelCycle a).Marked x) :
    Port.label H.jointLabel x = (numberedWheelCycles oddWheelCycle).edge 0 ∨
      Port.label H.jointLabel x = (numberedWheelCycles oddWheelCycle).edge 1 := by
  have hlabels (i : Fin (closedSigmaRimCircuit H oddWheelCycle a).length) :
      Port.label H.jointLabel ((closedSigmaRimCircuit H oddWheelCycle a).dart i) =
          (numberedWheelCycles oddWheelCycle).edge 0 ∨
        Port.label H.jointLabel ((closedSigmaRimCircuit H oddWheelCycle a).dart i) =
          (numberedWheelCycles oddWheelCycle).edge 1 := by
    obtain ⟨k, hk, he⟩ := hi i
    have hki : k = 0 ∨ k = 1 := by
      by_cases hzero : k.val = 0
      · exact Or.inl (Fin.ext hzero)
      · exact Or.inr (Fin.ext (by omega))
    rcases hki with rfl | rfl
    · exact Or.inl he.symm
    · exact Or.inr he.symm
  obtain ⟨⟨i, b⟩, rfl⟩ := hx
  cases b
  · exact hlabels i
  · simpa only [SimpleCircuit.port, SimpleCircuit.incoming, H.pairing.label_twin] using
      hlabels ((finRotate (closedSigmaRimCircuit H oddWheelCycle a).length).symm i)

include hi in
theorem oddIndependent_hub_label (i : Fin (closedSigmaRimCircuit H oddWheelCycle a).length) :
    H.hubLabel ((closedSigmaRimCircuit H oddWheelCycle a).hubAt i) = rowEquiv oddRow := by
  let C := closedSigmaRimCircuit H oddWheelCycle a
  have hinc (b : Bool) : Port.label H.jointLabel (C.port (i, b)) ∈
      numberedSystem.hypergraph.incidence (H.hubLabel (C.hubAt i)) := by
    obtain ⟨p, hp⟩ := C.port_eq_hubAt i b
    exact (numberedSystem.mem_hypergraph_incidence _ _).mpr
      ⟨p, (SolutionGroup.rowGraph_port_label numberedSystem H (C.hubAt i) p).symm.trans
        (congrArg (Port.label H.jointLabel) hp).symm⟩
  have hne : Port.label H.jointLabel (C.port (i, false)) ≠ Port.label H.jointLabel (C.port (i, true)) := by
    intro he
    have hp := H.row_label_injective_at_vertex ((C.port_vertex (i, false)).trans (C.port_vertex (i, true)).symm) he
    exact C.incoming_ne_outgoing i hp.symm
  rcases oddIndependent_marked_labels a hi ⟨(i, false), rfl⟩ with hx | hx
  · rcases oddIndependent_marked_labels a hi ⟨(i, true), rfl⟩ with hy | hy
    · exact (hne (hx.trans hy.symm)).elim
    · exact odd_independent_edges_common_row _ (hx ▸ hinc false) (hy ▸ hinc true)
  · rcases oddIndependent_marked_labels a hi ⟨(i, true), rfl⟩ with hy | hy
    · exact odd_independent_edges_common_row _ (hy ▸ hinc true) (hx ▸ hinc false)
    · exact (hne (hx.trans hy.symm)).elim

include hi in
theorem oddIndependent_hub_port_label (i : Fin (closedSigmaRimCircuit H oddWheelCycle a).length) (p : Fin 3) :
    Port.label H.jointLabel (.hub ((closedSigmaRimCircuit H oddWheelCycle a).hubAt i) p : H.Dart) =
      numberedSystem.column (rowEquiv oddRow) p :=
  (SolutionGroup.rowGraph_port_label numberedSystem H _ p).trans
    (congrArg (fun r => numberedSystem.column r p) (oddIndependent_hub_label a hi i))

include hi in
theorem oddIndependent_hub_port_marked (i : Fin (closedSigmaRimCircuit H oddWheelCycle a).length) (p : Fin 3) :
    (closedSigmaRimCircuit H oddWheelCycle a).Marked
      (.hub ((closedSigmaRimCircuit H oddWheelCycle a).hubAt i) p) ↔ p ≠ 0 := by
  let C := closedSigmaRimCircuit H oddWheelCycle a
  have hm (hp : p ≠ 0) : C.Marked (.hub (C.hubAt i) p) := by
    apply H.rimSimpleCircuit_marked_of_vertex_label (numberedWheelCycles oddWheelCycle) a
    · exact ⟨i, C.hubAt_vertex i⟩
    · have hl := oddIndependent_hub_port_label a hi i p
      fin_cases p
      · exact (hp rfl).elim
      · exact ⟨0, (hl.trans odd_row_column_one).symm⟩
      · exact ⟨1, (hl.trans odd_row_column_two).symm⟩
  refine ⟨?_, hm⟩
  rintro hmark rfl
  have hl := C.marked_label_rim (numberedWheelCycles oddWheelCycle)
    (H.rimSimpleCircuit_rim (numberedWheelCycles oddWheelCycle)
      (numberedWheelCycles oddWheelCycle).empty_boundary_no_rim
      (numberedWheelCycles oddWheelCycle).empty_boundary_no_rim a) hmark
  exact odd_row_spoke_not_cycle oddWheelCycle ((oddIndependent_hub_port_label a hi i 0) ▸ hl)

include hi in
theorem oddIndependent_slot_one_partner (i : Fin (closedSigmaRimCircuit H oddWheelCycle a).length) :
    ∃ j : Fin (closedSigmaRimCircuit H oddWheelCycle a).length,
      H.pairing.twin (.hub ((closedSigmaRimCircuit H oddWheelCycle a).hubAt i) (1 : Fin 3)) =
        .hub ((closedSigmaRimCircuit H oddWheelCycle a).hubAt j) (1 : Fin 3) := by
  let C := closedSigmaRimCircuit H oddWheelCycle a
  have hm : C.Marked (.hub (C.hubAt i) (1 : Fin 3)) :=
    (oddIndependent_hub_port_marked a hi i 1).mpr (by decide +kernel)
  obtain ⟨j, hj⟩ := C.marked_onCircuitVertex ((C.marked_twin_iff _).mpr hm)
  refine ⟨j, H.row_label_injective_at_vertex (hj.symm.trans (C.hubAt_vertex j)) ?_⟩
  exact (H.pairing.label_twin _).trans
    ((oddIndependent_hub_port_label a hi i 1).trans (oddIndependent_hub_port_label a hi j 1).symm)

noncomputable def oddIndependentPartner (i : Fin (closedSigmaRimCircuit H oddWheelCycle a).length) :
    Fin (closedSigmaRimCircuit H oddWheelCycle a).length := (oddIndependent_slot_one_partner a hi i).choose

theorem oddIndependentPartner_paired (i : Fin (closedSigmaRimCircuit H oddWheelCycle a).length) :
    H.pairing.twin (.hub ((closedSigmaRimCircuit H oddWheelCycle a).hubAt i) (1 : Fin 3)) =
      .hub ((closedSigmaRimCircuit H oddWheelCycle a).hubAt (oddIndependentPartner a hi i)) (1 : Fin 3) :=
  (oddIndependent_slot_one_partner a hi i).choose_spec

theorem oddIndependentPartner_involutive : Function.Involutive (oddIndependentPartner a hi) := by
  intro i
  have he := (oddIndependentPartner_paired a hi (oddIndependentPartner a hi i)).symm.trans
    ((congrArg H.pairing.twin (oddIndependentPartner_paired a hi i)).symm.trans (H.pairing.involutive _))
  exact (closedSigmaRimCircuit H oddWheelCycle a).hubAt_injective
    (Sum.inl.inj (Sum.inr.inj (congrArg Port.vertex he)))

theorem oddIndependentPartner_ne_self (i : Fin (closedSigmaRimCircuit H oddWheelCycle a).length) :
    oddIndependentPartner a hi i ≠ i := by
  intro he
  have hp := oddIndependentPartner_paired a hi i
  rw [he] at hp
  exact H.pairing.ne_self _ hp

noncomputable def oddIndependentPairing :
    Pairing (fun i : Fin (closedSigmaRimCircuit H oddWheelCycle a).length =>
      H.hubLabel ((closedSigmaRimCircuit H oddWheelCycle a).hubAt i)) where
  twin := oddIndependentPartner a hi
  involutive := oddIndependentPartner_involutive a hi
  ne_self := oddIndependentPartner_ne_self a hi
  label_twin i := (oddIndependent_hub_label a hi _).trans (oddIndependent_hub_label a hi i).symm

include hi in
theorem oddIndependent_length_even : Even (closedSigmaRimCircuit H oddWheelCycle a).length := by
  refine ⟨Fintype.card (oddIndependentPairing a hi).Edge, ?_⟩
  simpa only [Fintype.card_fin, two_mul] using (oddIndependentPairing a hi).dart_card_eq_twice_edge_card

include hi in
theorem oddIndependent_removed_weight_zero (χ : Fin 1417152 → ZMod 2) :
    (∑ i : Fin (closedSigmaRimCircuit H oddWheelCycle a).length,
      χ (H.hubLabel ((closedSigmaRimCircuit H oddWheelCycle a).hubAt i))) = 0 :=
  (oddIndependentPairing a hi).sum_charge χ

include hi in
theorem oddIndependent_erased_weight (χ : Fin 1417152 → ZMod 2) :
    (∑ h : (closedSigmaRimCircuit H oddWheelCycle a).ErasedCircuitHub, χ (H.hubLabel h.val)) =
      ∑ h : H.Hub, χ (H.hubLabel h) := by
  have he := (closedSigmaRimCircuit H oddWheelCycle a).erasedCircuitHub_sum (fun h => χ (H.hubLabel h))
  rw [oddIndependent_removed_weight_zero a hi χ, add_zero] at he
  exact he

end ThomGame.Construction
