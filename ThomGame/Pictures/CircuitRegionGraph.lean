module

public import ThomGame.Pictures.CircuitFrontier

/-!
# The actual port graph on one side after removing circuit vertices

Unmarked edges on the selected cut side are retained, including chords
with both ends on the circuit. Internal hubs and junctions retain every
port and their labels. The frontier ports become boundary leaves in the
order already proved for the twisted rotation. The construction concerns
the original component of the circuit; it makes no placement claim about
other disconnected components. Diagram witnesses are constructed
separately in `CircuitRegionDiagram`, preserving boundary and hub labels
without asserting a graph isomorphism.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open Equiv RibbonConnectivity
open scoped Classical

section General

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  {G : PortGraph P u v} (C : G.SimpleCircuit)

def KeptDart (s : Bool) (a : G.Dart) : Prop := ¬ C.Marked a ∧ C.OnSide s a

def InteriorVertex (s : Bool) (x : G.Vertex) : Prop :=
  ¬ C.OnCircuitVertex x ∧ ∃ a : G.Dart, a.vertex = x ∧ C.OnSide s a

theorem keptDart_twin_iff (s : Bool) (a : G.Dart) :
    C.KeptDart s (G.pairing.twin a) ↔ C.KeptDart s a := by
  constructor
  · rintro ⟨ha, hs⟩
    have hn : ¬ C.Marked a := fun hm => ha ((C.marked_twin_iff a).mpr hm)
    exact ⟨hn, (C.onSide_twin_iff hn s).mp hs⟩
  · rintro ⟨ha, hs⟩
    exact ⟨fun hm => ha ((C.marked_twin_iff a).mp hm), (C.onSide_twin_iff ha s).mpr hs⟩

noncomputable def keptPairing (s : Bool) :
    Pairing (fun a : Subtype (C.KeptDart s) => Port.label G.jointLabel a.val) where
  twin a := ⟨G.pairing.twin a.val, (C.keptDart_twin_iff s a.val).mpr a.property⟩
  involutive a := Subtype.ext (G.pairing.involutive a.val)
  ne_self a h := G.pairing.ne_self a.val (congrArg Subtype.val h)
  label_twin a := G.pairing.label_twin a.val

theorem interior_port_kept (s : Bool) {x : G.Vertex} (hx : C.InteriorVertex s x)
    (a : G.Dart) (ha : a.vertex = x) : C.KeptDart s a := by
  obtain ⟨hn, b, hb, hs⟩ := hx
  have hna : ¬ C.OnCircuitVertex a.vertex := fun h => hn (ha ▸ h)
  have hnb : ¬ C.OnCircuitVertex b.vertex := fun h => hn (hb ▸ h)
  exact ⟨fun hm => hna (C.marked_onCircuitVertex hm),
    (C.onSide_same_vertex hnb (hb.trans ha.symm) s).mp hs⟩

abbrev InteriorHub (s : Bool) := {h : G.Hub // C.InteriorVertex s (.inr (.inl h))}
abbrev InteriorJoint (s : Bool) := {j : G.Joint // C.InteriorVertex s (.inr (.inr j))}

noncomputable instance interiorHubFintype (s : Bool) : Fintype (C.InteriorHub s) :=
  inferInstanceAs (Fintype {h : G.Hub // C.InteriorVertex s (.inr (.inl h))})

noncomputable instance interiorJointFintype (s : Bool) : Fintype (C.InteriorJoint s) :=
  inferInstanceAs (Fintype {j : G.Joint // C.InteriorVertex s (.inr (.inr j))})

abbrev RegionPort (s : Bool) :=
  Port P (C.frontierWord s) [] (C.InteriorHub s) (C.InteriorJoint s) (fun h => G.hubLabel h.val)

variable (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
  2 * Nat.card (Component G.circuitStep G.pairing.perm))

noncomputable def regionPortMap (s : Bool) : C.RegionPort s → Subtype (C.KeptDart s)
  | .top i => ⟨(C.boundaryEnumeration s i).val,
      ((C.frontier_iff hEuler s _).mp (C.boundaryEnumeration s i).property).2⟩
  | .bottom i => i.elim0
  | .hub h i => ⟨.hub h.val i, C.interior_port_kept s h.property (.hub h.val i) rfl⟩
  | .joint j b => ⟨.joint j.val b, C.interior_port_kept s j.property (.joint j.val b) rfl⟩

include hEuler in
theorem regionPortMap_label (s : Bool) (a : C.RegionPort s) :
    Port.label G.jointLabel (C.regionPortMap hEuler s a).val =
      Port.label (fun j : C.InteriorJoint s => G.jointLabel j.val) a := by
  cases a with
  | top i => exact C.boundaryEnumeration_label s i
  | bottom i => exact i.elim0
  | hub h i => rfl
  | joint j b => rfl

include hEuler in
theorem regionPortMap_injective (s : Bool) : Function.Injective (C.regionPortMap hEuler s) := by
  intro a b he
  have hd := congrArg Subtype.val he
  have hv := congrArg Port.vertex hd
  cases a with
  | top i =>
    have hi := ((C.frontier_iff hEuler s _).mp (C.boundaryEnumeration s i).property).1
    cases b with
    | top j => exact congrArg Port.top ((C.boundaryEnumeration s).injective (Subtype.ext hd))
    | bottom j => exact j.elim0
    | hub h j => exact (h.property.1 ((congrArg C.OnCircuitVertex hv).mp hi)).elim
    | joint j t => exact (j.property.1 ((congrArg C.OnCircuitVertex hv).mp hi)).elim
  | bottom i => exact i.elim0
  | hub h i =>
    cases b with
    | top j =>
      have hj := ((C.frontier_iff hEuler s _).mp (C.boundaryEnumeration s j).property).1
      exact (h.property.1 ((congrArg C.OnCircuitVertex hv.symm).mp hj)).elim
    | bottom j => exact j.elim0
    | hub k j =>
      rcases h with ⟨h, hh⟩
      rcases k with ⟨k, hk⟩
      change (Port.hub h i : G.Dart) = .hub k j at hd
      cases hd
      rfl
    | joint j t => cases hd
  | joint j t =>
    cases b with
    | top i =>
      have hi := ((C.frontier_iff hEuler s _).mp (C.boundaryEnumeration s i).property).1
      exact (j.property.1 ((congrArg C.OnCircuitVertex hv.symm).mp hi)).elim
    | bottom i => exact i.elim0
    | hub h i => cases hd
    | joint k w =>
      rcases j with ⟨j, hj⟩
      rcases k with ⟨k, hk⟩
      change (Port.joint j t : G.Dart) = .joint k w at hd
      cases hd
      rfl

end General

section Closed

variable {R S : Type*} {P : InvolutionPresentation R S}
  {G : PortGraph P [] []} (C : G.SimpleCircuit)
variable (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
  2 * Nat.card (Component G.circuitStep G.pairing.perm))

noncomputable def regionPortInv (s : Bool) (a : Subtype (C.KeptDart s)) : C.RegionPort s := by
  by_cases hv : C.OnCircuitVertex a.val.vertex
  · exact .top ((C.boundaryEnumeration s).symm
      ⟨a.val, (C.frontier_iff hEuler s a.val).mpr ⟨hv, a.property⟩⟩)
  · rcases a with ⟨a, ha⟩
    cases a with
    | top i => exact i.elim0
    | bottom i => exact i.elim0
    | hub h i => exact .hub ⟨h, hv, .hub h i, rfl, ha.2⟩ i
    | joint j b => exact .joint ⟨j, hv, .joint j b, rfl, ha.2⟩ b

include hEuler in
theorem regionPortMap_inv (s : Bool) (a : Subtype (C.KeptDart s)) :
    C.regionPortMap hEuler s (C.regionPortInv hEuler s a) = a := by
  by_cases hv : C.OnCircuitVertex a.val.vertex
  · apply Subtype.ext
    simp only [regionPortInv, dite_eq_left hv, regionPortMap, Equiv.apply_symm_apply]
  · rcases a with ⟨a, ha⟩
    cases a with
    | top i => exact i.elim0
    | bottom i => exact i.elim0
    | hub h i => simp only [regionPortInv, dite_eq_right hv, regionPortMap]
    | joint j b => simp only [regionPortInv, dite_eq_right hv, regionPortMap]

include hEuler in
theorem regionPortInv_map (s : Bool) (a : C.RegionPort s) :
    C.regionPortInv hEuler s (C.regionPortMap hEuler s a) = a :=
  C.regionPortMap_injective hEuler s (C.regionPortMap_inv hEuler s _)

noncomputable def regionPorts (s : Bool) : C.RegionPort s ≃ Subtype (C.KeptDart s) where
  toFun := C.regionPortMap hEuler s
  invFun := C.regionPortInv hEuler s
  left_inv := C.regionPortInv_map hEuler s
  right_inv := C.regionPortMap_inv hEuler s

@[reducible] noncomputable def regionGraph (s : Bool) : PortGraph P (C.frontierWord s) [] where
  Hub := C.InteriorHub s
  Joint := C.InteriorJoint s
  hubLabel h := G.hubLabel h.val
  hubFlip h := G.hubFlip h.val
  jointLabel j := G.jointLabel j.val
  pairing := (C.keptPairing s).transport (C.regionPorts hEuler s).symm _ (by
    intro a
    obtain ⟨b, rfl⟩ := (C.regionPorts hEuler s).surjective a
    rw [Equiv.symm_apply_apply]
    change Port.label (fun j : C.InteriorJoint s => G.jointLabel j.val) b =
      Port.label G.jointLabel (C.regionPortMap hEuler s b).val
    exact (C.regionPortMap_label hEuler s b).symm)

include hEuler in
theorem regionGraph_twin (s : Bool) (a : (C.regionGraph hEuler s).Dart) :
    (C.regionPorts hEuler s ((C.regionGraph hEuler s).pairing.twin a)).val =
      G.pairing.twin (C.regionPorts hEuler s a).val := by
  simp only [regionGraph, Pairing.transport, Equiv.symm_symm, Equiv.apply_symm_apply]
  rfl

include hEuler in
theorem regionGraph_hub_rotation (s : Bool) (h : (C.regionGraph hEuler s).Hub)
    (i : Fin (P.word ((C.regionGraph hEuler s).hubLabel h)).length) :
    (C.regionPorts hEuler s ((C.regionGraph hEuler s).rotation (.hub h i))).val =
      G.rotation (C.regionPorts hEuler s (.hub h i)).val := rfl

include hEuler in
theorem regionGraph_joint_rotation (s : Bool) (j : (C.regionGraph hEuler s).Joint) (b : Bool) :
    (C.regionPorts hEuler s ((C.regionGraph hEuler s).rotation (.joint j b))).val =
      G.rotation (C.regionPorts hEuler s (.joint j b)).val := rfl

include hEuler in
theorem regionGraph_boundary (s : Bool) (i : Fin (C.frontierWord s).length) :
    (C.regionPorts hEuler s (.top i)).val = (C.boundaryEnumeration s i).val := rfl

end Closed
end ThomGame.Pictures.PortGraph.SimpleCircuit
