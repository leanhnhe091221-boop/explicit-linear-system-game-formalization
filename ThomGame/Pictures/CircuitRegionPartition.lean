module

public import ThomGame.Pictures.CircuitRegionCharge

/-!
# Partitioning the original circuit component into its two regions

Each incident vertex of the original component belongs either to the
circuit or to exactly one of the two interior vertex sets. Summing any
vertex weight gives the corresponding decomposition; in particular this
tracks actual relation counts and signs without assigning unrelated
disconnected components to a side.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open RibbonConnectivity
open scoped BigOperators Classical

section General

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  {G : PortGraph P u v} (C : G.SimpleCircuit)

def InCircuitComponent (x : G.Vertex) : Prop :=
  ∃ a : G.Dart, a.vertex = x ∧ Connected G.circuitStep G.pairing.perm a C.cutBase

abbrev ComponentHub := {h : G.Hub // C.InCircuitComponent (.inr (.inl h))}
abbrev CircuitHub := {h : G.Hub // C.OnCircuitVertex (.inr (.inl h))}

noncomputable instance componentHubFintype : Fintype C.ComponentHub :=
  inferInstanceAs (Fintype {h : G.Hub // C.InCircuitComponent (.inr (.inl h))})

noncomputable instance circuitHubFintype : Fintype C.CircuitHub :=
  inferInstanceAs (Fintype {h : G.Hub // C.OnCircuitVertex (.inr (.inl h))})

theorem old_connected_base_iff_onSide (a : G.Dart) :
    Connected G.circuitStep G.pairing.perm a C.cutBase ↔ ∃ s, C.OnSide s a := by
  rw [C.old_connected_base_iff]
  constructor
  · rintro (h | h)
    · exact ⟨false, h⟩
    · exact ⟨true, h.trans (C.cut_port_true_mate 0).symm⟩
  · rintro ⟨s, hs⟩
    cases s
    · exact Or.inl hs
    · exact Or.inr (hs.trans (C.cut_port_true_mate 0))

theorem circuitVertex_in_component {x : G.Vertex} (hx : C.OnCircuitVertex x) :
    C.InCircuitComponent x := by
  obtain ⟨i, hi⟩ := hx
  exact ⟨C.dart i, hi, C.cut_connected_old (C.cut_port_false_base i)⟩

theorem interiorVertex_in_component {s : Bool} {x : G.Vertex} (hx : C.InteriorVertex s x) :
    C.InCircuitComponent x := by
  obtain ⟨_, a, ha, hs⟩ := hx
  exact ⟨a, ha, (C.old_connected_base_iff_onSide a).mpr ⟨s, hs⟩⟩

theorem component_vertex_partition (x : G.Vertex) :
    C.InCircuitComponent x ↔ C.OnCircuitVertex x ∨ C.InteriorVertex false x ∨ C.InteriorVertex true x := by
  constructor
  · rintro ⟨a, ha, hc⟩
    by_cases hx : C.OnCircuitVertex x
    · exact Or.inl hx
    · obtain ⟨s, hs⟩ := (C.old_connected_base_iff_onSide a).mp hc
      cases s
      · exact Or.inr (Or.inl ⟨hx, a, ha, hs⟩)
      · exact Or.inr (Or.inr ⟨hx, a, ha, hs⟩)
  · rintro (h | h | h)
    · exact C.circuitVertex_in_component h
    · exact C.interiorVertex_in_component h
    · exact C.interiorVertex_in_component h

variable (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
  2 * Nat.card (Component G.circuitStep G.pairing.perm))

include hEuler in
theorem interiorVertex_side_unique {x : G.Vertex} {s t : Bool}
    (hs : C.InteriorVertex s x) (ht : C.InteriorVertex t x) : s = t := by
  obtain ⟨_, a, ha, hsa⟩ := hs
  have hta := (C.interior_port_kept t ht a ha).2
  exact C.onSide_unique hEuler hsa hta

theorem subtype_sum_indicator {A B : Type*} [Fintype A] [AddCommMonoid B]
    (p : A → Prop) (w : A → B) :
    (∑ a : Subtype p, w a.val) = ∑ a, if p a then w a else 0 := by
  have h := (Finset.sum_subtype (F := inferInstance) (Finset.univ.filter p)
    (by simp : ∀ a, a ∈ Finset.univ.filter p ↔ p a) w).symm
  simpa only [Finset.sum_filter] using h

include hEuler in
theorem component_hub_sum {B : Type*} [AddCommMonoid B] (w : G.Hub → B) :
    (∑ h : C.ComponentHub, w h.val) = (∑ h : C.CircuitHub, w h.val) +
      (∑ h : C.InteriorHub false, w h.val) + (∑ h : C.InteriorHub true, w h.val) := by
  rw [subtype_sum_indicator, subtype_sum_indicator, subtype_sum_indicator, subtype_sum_indicator,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _
  let x : G.Vertex := .inr (.inl h)
  change (if C.InCircuitComponent x then w h else 0) =
    (if C.OnCircuitVertex x then w h else 0) + (if C.InteriorVertex false x then w h else 0) +
      (if C.InteriorVertex true x then w h else 0)
  by_cases hc : C.OnCircuitVertex x
  · have hi0 : ¬ C.InteriorVertex false x := fun hi => hi.1 hc
    have hi1 : ¬ C.InteriorVertex true x := fun hi => hi.1 hc
    have hp := C.circuitVertex_in_component hc
    simp only [hp, hc, hi0, hi1,
      ite_true, ite_false, add_zero]
  · by_cases hi0 : C.InteriorVertex false x
    · have hi1 : ¬ C.InteriorVertex true x := by
        intro hi1
        have he := C.interiorVertex_side_unique hEuler hi0 hi1
        cases he
      have hp := C.interiorVertex_in_component hi0
      simp only [hp, hc, hi0, hi1,
        ite_true, ite_false, zero_add, add_zero]
    · by_cases hi1 : C.InteriorVertex true x
      · have hp := C.interiorVertex_in_component hi1
        simp only [hp, hc, hi0, hi1,
          ite_true, ite_false, zero_add]
      · have hp : ¬ C.InCircuitComponent x := by
          intro hx
          rcases (C.component_vertex_partition x).mp hx with hh | hh | hh
          · exact hc hh
          · exact hi0 hh
          · exact hi1 hh
        simp only [hp, hc, hi0, hi1,
          ite_false, add_zero]

include hEuler in
theorem component_hub_card :
    Nat.card C.ComponentHub = Nat.card C.CircuitHub +
      Nat.card (C.InteriorHub false) + Nat.card (C.InteriorHub true) := by
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
    Nat.card_eq_fintype_card] using C.component_hub_sum hEuler (fun _ => (1 : Nat))

end General

section Closed

variable {R S : Type*} {P : InvolutionPresentation R S} {G : PortGraph P [] []} (C : G.SimpleCircuit)
  (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
    2 * Nat.card (RibbonConnectivity.Component G.circuitStep G.pairing.perm))

include hEuler in
theorem regionGraph_sign_partition :
    (∑ h : C.ComponentHub, P.parity (G.hubLabel h.val)) =
      (∑ h : C.CircuitHub, P.parity (G.hubLabel h.val)) +
        (C.regionGraph hEuler false).sign + (C.regionGraph hEuler true).sign :=
  C.component_hub_sum hEuler (fun h => P.parity (G.hubLabel h))

include hEuler in
theorem regionGraph_character_partition [DecidableEq R] (r : R) :
    (∑ h : C.ComponentHub, if G.hubLabel h.val = r then (1 : ZMod 2) else 0) =
      (∑ h : C.CircuitHub, if G.hubLabel h.val = r then (1 : ZMod 2) else 0) +
        (C.regionGraph hEuler false).character r + (C.regionGraph hEuler true).character r := by
  rw [(C.regionGraph hEuler false).character_eq_sum, (C.regionGraph hEuler true).character_eq_sum]
  exact C.component_hub_sum hEuler (fun h => if G.hubLabel h = r then (1 : ZMod 2) else 0)

end Closed
end ThomGame.Pictures.PortGraph.SimpleCircuit
