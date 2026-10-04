module

public import ThomGame.Pictures.CircuitSectorBlocks
public import ThomGame.Pictures.DisconnectedBlockFamily
public import ThomGame.Pictures.ConnectedGraphRealization

/-!
# Genuine diagrams for the two actual circuit regions

The invariant capped sector is partitioned into one auxiliary boundary
block and the actual interior hubs and joints. Closing its block family
and puncturing the unique auxiliary relation produces the existing
frontier word, with exactly the interior relation multiset. Neither
connectivity nor extra Euler or boundary conditions on the region are
assumed. The conclusion is a diagram witness, not a graph isomorphism.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open Equiv RibbonConnectivity
open scoped Classical BigOperators

variable {R S : Type*} {P : InvolutionPresentation R S} {G : PortGraph P [] []}
    (C : G.SimpleCircuit)

abbrev SectorIndex (s : Bool) := Option (C.InteriorHub s ⊕ C.InteriorJoint s)

noncomputable def sectorOwner (s : Bool) (a : C.CappedDart s) : C.SectorIndex s := by
  by_cases hv : C.OnCircuitVertex a.val.vertex
  · exact none
  · have hi : C.InteriorVertex s a.val.vertex :=
      ⟨hv, a.val, rfl, (C.cappedSide_iff_onSide
        (fun hm => hv (C.marked_onCircuitVertex hm)) s).mp a.property⟩
    rcases a with ⟨a, ha⟩
    cases a with
    | top i => exact i.elim0
    | bottom i => exact i.elim0
    | hub h _ => exact some (.inl ⟨h, hi⟩)
    | joint j _ => exact some (.inr ⟨j, hi⟩)

theorem sectorOwner_none_iff (s : Bool) (a : C.CappedDart s) :
    C.sectorOwner s a = none ↔ C.OnCircuitVertex a.val.vertex := by
  unfold sectorOwner
  split_ifs with hv
  · simp only [hv]
  · rcases a with ⟨a, ha⟩
    cases a with
    | top i => exact i.elim0
    | bottom i => exact i.elim0
    | hub h i => simp only [reduceCtorEq, hv]
    | joint j b => simp only [reduceCtorEq, hv]

theorem sectorOwner_hub_iff (s : Bool) (h : C.InteriorHub s) (a : C.CappedDart s) :
    C.sectorOwner s a = some (.inl h) ↔ ∃ i, Port.hub h.val i = a.val := by
  by_cases hv : C.OnCircuitVertex a.val.vertex
  · have hn : ¬ ∃ i, Port.hub h.val i = a.val := by
      rintro ⟨i, hi⟩
      rw [← hi] at hv
      exact h.property.1 hv
    simp only [sectorOwner, dite_eq_left hv, reduceCtorEq, hn]
  · rcases a with ⟨a, ha⟩
    cases a with
    | top i => exact i.elim0
    | bottom i => exact i.elim0
    | hub k j =>
      simp only [sectorOwner, dite_eq_right hv, Option.some.injEq, Sum.inl.injEq, Subtype.ext_iff]
      constructor
      · intro he
        subst k
        exact ⟨j, rfl⟩
      · rintro ⟨i, he⟩
        cases he
        rfl
    | joint j b => simp only [sectorOwner, dite_eq_right hv, Option.some.injEq, reduceCtorEq,
        exists_false]

theorem sectorOwner_joint_iff (s : Bool) (j : C.InteriorJoint s) (a : C.CappedDart s) :
    C.sectorOwner s a = some (.inr j) ↔ ∃ b, Port.joint j.val b = a.val := by
  by_cases hv : C.OnCircuitVertex a.val.vertex
  · have hn : ¬ ∃ b, Port.joint j.val b = a.val := by
      rintro ⟨b, hb⟩
      rw [← hb] at hv
      exact j.property.1 hv
    simp only [sectorOwner, dite_eq_left hv, reduceCtorEq, hn]
  · rcases a with ⟨a, ha⟩
    cases a with
    | top i => exact i.elim0
    | bottom i => exact i.elim0
    | hub h i => simp only [sectorOwner, dite_eq_right hv, Option.some.injEq, reduceCtorEq,
        exists_false]
    | joint k b =>
      simp only [sectorOwner, dite_eq_right hv, Option.some.injEq, Sum.inr.injEq, Subtype.ext_iff]
      constructor
      · intro he
        exact ⟨b, by rw [← he]⟩
      · rintro ⟨b', he⟩
        cases he
        rfl

variable (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
  2 * Nat.card (Component G.circuitStep G.pairing.perm))

include hEuler in
theorem sectorOuterBlock_mem_owner (s : Bool) (a : C.CappedDart s) :
    a ∈ (C.sectorOuterBlock s).ports ↔ C.sectorOwner s a = none := by
  rw [C.sectorOuterBlock_mem, C.sectorOwner_none_iff]
  exact ⟨fun ha => (C.onCircuitVertex_iff_sector a.val).mpr ⟨!s, ha⟩,
    fun hv => (C.cappedSide_sector_iff hEuler hv s).mp a.property⟩

noncomputable def sectorBlockFamily (s : Bool)
    (hn : ∀ h : C.InteriorHub s, 0 < (P.word (G.hubLabel h.val)).length) :
    BlockFamily (P.adjoinRelation (C.frontierWord s) 0)
      (fun a : C.CappedDart s => Port.label G.jointLabel a.val)
      (C.sectorRotation s) (C.sectorPairing s) where
  Index := C.SectorIndex s
  block
    | none => C.sectorOuterBlock s
    | some (.inl h) => C.sectorHubBlock s h (hn h)
    | some (.inr j) => C.sectorJointBlock s j
  owner := C.sectorOwner s
  mem_ports a i := by
    rcases i with _ | (h | j)
    · exact C.sectorOuterBlock_mem_owner hEuler s a
    · exact (C.sectorHubBlock_mem s h (hn h) a).trans (C.sectorOwner_hub_iff s h a).symm
    · exact (C.sectorJointBlock_mem s j a).trans (C.sectorOwner_joint_iff s j a).symm

include hEuler in
theorem sectorBlockFamily_relations (s : Bool)
    (hn : ∀ h : C.InteriorHub s, 0 < (P.word (G.hubLabel h.val)).length) :
    (C.sectorBlockFamily hEuler s hn).relations =
      {none} + (∑ h : C.InteriorHub s, ([G.hubLabel h.val] : Multiset R)).map some := by
  unfold BlockFamily.relations sectorBlockFamily
  rw [Fintype.sum_option, Fintype.sum_sum_type]
  simp only [C.sectorOuterBlock_labels, C.sectorHubBlock_labels, C.sectorJointBlock_labels,
    Multiset.coe_nil, Finset.sum_const_zero, add_zero]
  congr 1
  let f : Multiset R →+ Multiset (Option R) := {
    toFun := Multiset.map some
    map_zero' := rfl
    map_add' := Multiset.map_add some }
  exact (map_sum f (fun h : C.InteriorHub s => ([G.hubLabel h.val] : Multiset R)) Finset.univ).symm

include hEuler in
theorem exists_region_diagram (s : Bool)
    (hn : ∀ h : C.InteriorHub s, 0 < (P.word (G.hubLabel h.val)).length) :
    ∃ d : Diagram P (C.frontierWord s) [],
      (d.labels : Multiset R) = ∑ h : C.InteriorHub s, ([G.hubLabel h.val] : Multiset R) := by
  obtain ⟨d, hd⟩ := (C.sectorBlockFamily hEuler s hn).exists_closed_diagram_of_saturated
    (C.sectorPairing_involutive s) (C.sectorPairing_label s) (C.capped_sector_saturated hEuler s)
  exact d.exists_punctured_diagram_of_multiset _ (hd.trans (C.sectorBlockFamily_relations hEuler s hn))

include hEuler in
theorem exists_region_diagram_preserving (s : Bool)
    (hn : ∀ h : C.InteriorHub s, 0 < (P.word (G.hubLabel h.val)).length) :
    ∃ d : Diagram P (C.frontierWord s) [],
      (d.labels : Multiset R) = (∑ h : C.InteriorHub s, ([G.hubLabel h.val] : Multiset R)) ∧
      d.size = Fintype.card (C.InteriorHub s) ∧ d.sign = (C.regionGraph hEuler s).sign := by
  obtain ⟨d, hd⟩ := C.exists_region_diagram hEuler s hn
  exact ⟨d, hd, (C.regionGraph hEuler s).diagram_size_of_hub_labels hd,
    (C.regionGraph hEuler s).diagram_sign_of_hub_labels hd⟩

end ThomGame.Pictures.PortGraph.SimpleCircuit
