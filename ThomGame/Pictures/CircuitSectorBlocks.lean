module

public import ThomGame.Pictures.CircuitSectorEuler
public import ThomGame.Pictures.SubtypeDiagramBlock
public import ThomGame.Pictures.ClosedGraphBlocks
public import ThomGame.Pictures.DistinguishedRelation

/-!
# Actual diagram blocks for a capped circuit region

One auxiliary relation accounts for the selected sector's exact frontier
word. Every interior hub contributes its original relation once; every
interior subdivision joint contributes a relation-free cap. All blocks
are restricted to the actual invariant capped-side port set.
-/

@[expose] public section
namespace ThomGame.Pictures

open Equiv CyclicBlock
open scoped Classical

namespace OrbitEnumeration

variable {D : Type*} [Finite D] (f : Perm D) (a : D) (p : D → Prop)

theorem retainedList_eq_filter :
    retainedList f a p = (List.ofFn (dart f a)).filter (fun x => decide (p x)) := by
  change (List.ofFn (fun i : Fin (Nat.card (Subtype (retainedIndices f a p))) =>
    dart f a (CircularPartition.subsetEnumeration (retainedIndices f a p) i).val)) = _
  rw [List.ofFn_comp' _ (dart f a), CircularPartition.subsetEnumeration_list]
  simp only [List.ofFn_eq_map, List.filter_map, Function.comp_def, retainedIndices]
  rfl

end OrbitEnumeration

namespace PortGraph.SimpleCircuit

variable {R S : Type*} {P : InvolutionPresentation R S} {G : PortGraph P [] []}
    (C : G.SimpleCircuit)

noncomputable def sectorPorts (s : Bool) : List G.Dart :=
  List.ofFn (OrbitEnumeration.dart (C.edgeTwist * G.rotation) (C.port (0, !s)))

theorem sectorPorts_cyclic (s : Bool) :
    IsCycleWord (C.edgeTwist * G.rotation) (C.sectorPorts s) :=
  IsCycleWord.ofFn _ _ (OrbitEnumeration.dart _ _).injective
    (OrbitEnumeration.length_pos _ _) (fun i => (OrbitEnumeration.dart_next _ _ i).symm)

theorem mem_sectorPorts (s : Bool) (a : G.Dart) : a ∈ C.sectorPorts s ↔ C.Sector (!s) a := by
  rw [sectorPorts, List.mem_ofFn]
  exact OrbitEnumeration.dart_range _ _ a

theorem sectorPorts_filter (s : Bool) :
    (C.sectorPorts s).filter (moving C.cutPairing) = C.frontierDarts s := by
  have hm : moving C.cutPairing = fun a => decide (¬ C.Marked a) := by
    funext a
    simp only [moving, ne_eq, C.cutPairing_fixed_iff]
  rw [hm]
  simpa only [sectorPorts, frontierDarts, decide_not] using
    (OrbitEnumeration.retainedList_eq_filter (C.edgeTwist * G.rotation)
      (C.port (0, !s)) (fun a => ¬ C.Marked a)).symm

theorem sectorPorts_boundary (s : Bool) :
    ((C.sectorPorts s).filter (moving C.cutPairing)).map (Port.label G.jointLabel) =
      C.frontierWord s := by
  rw [C.sectorPorts_filter]
  change (List.ofFn _).map _ = _
  rw [List.map_ofFn]
  rfl

abbrev SectorBlock (s : Bool) :=
  DiagramBlock (P.adjoinRelation (C.frontierWord s) 0)
    (fun a : C.CappedDart s => Port.label G.jointLabel a.val)
    (C.sectorRotation s) (C.sectorPairing s)

noncomputable def sectorOuterAmbient (s : Bool) :
    DiagramBlock (P.adjoinRelation (C.frontierWord s) 0) (Port.label G.jointLabel)
      (C.edgeTwist * G.rotation) C.cutPairing where
  ports := C.sectorPorts s
  cyclic := C.sectorPorts_cyclic s
  diagram := (Diagram.down (P := P.adjoinRelation (C.frontierWord s) 0) none).cast
    (C.sectorPorts_boundary s).symm rfl

noncomputable def sectorOuterBlock (s : Bool) : C.SectorBlock s :=
  (C.sectorOuterAmbient s).restrict (C.CappedSide s)
    (C.cappedSide_rotation_iff s) (C.cappedSide_pairing_iff s)
    (fun a ha => C.sector_cappedSide ((C.mem_sectorPorts s a).mp ha))

theorem sectorOuterBlock_labels (s : Bool) : (C.sectorOuterBlock s).diagram.labels = [none] := by
  exact ((C.sectorOuterAmbient s).restrict_labels (C.CappedSide s)
    (C.cappedSide_rotation_iff s) (C.cappedSide_pairing_iff s)
    (fun a ha => C.sector_cappedSide ((C.mem_sectorPorts s a).mp ha))).trans
      ((Diagram.down (P := P.adjoinRelation (C.frontierWord s) 0) none).labels_cast
        (C.sectorPorts_boundary s).symm rfl)

theorem sectorOuterBlock_mem (s : Bool) (a : C.CappedDart s) :
    a ∈ (C.sectorOuterBlock s).ports ↔ C.Sector (!s) a.val := by
  rw [sectorOuterBlock, DiagramBlock.restrict_mem]
  exact C.mem_sectorPorts s a.val

theorem hubBlock_interior (s : Bool) (h : C.InteriorHub s)
    (hn : 0 < (P.word (G.hubLabel h.val)).length)
    (a : G.Dart) (ha : a ∈ (G.hubBlock h.val hn).ports) : C.InteriorVertex s a.vertex := by
  obtain ⟨i, rfl⟩ := (G.hubBlock_mem h.val hn a).mp ha
  exact h.property

theorem filter_cutPairing_interior (s : Bool) (w : List G.Dart)
    (hw : ∀ a ∈ w, C.InteriorVertex s a.vertex) : w.filter (moving C.cutPairing) = w := by
  apply List.filter_eq_self.mpr
  intro a ha
  change decide (C.cutPairing a ≠ a) = true
  exact decide_eq_true (fun he => (hw a ha).1
    (C.marked_onCircuitVertex ((C.cutPairing_fixed_iff a).mp he)))

noncomputable def sectorHubAmbient (s : Bool) (h : C.InteriorHub s)
    (hn : 0 < (P.word (G.hubLabel h.val)).length) :
    DiagramBlock (P.adjoinRelation (C.frontierWord s) 0) (Port.label G.jointLabel)
      (C.edgeTwist * G.rotation) C.cutPairing where
  ports := (G.hubBlock h.val hn).ports
  cyclic := {
    nodup := (G.hubBlock h.val hn).cyclic.nodup
    nonempty := (G.hubBlock h.val hn).cyclic.nonempty
    rotation a ha := (C.twisted_rotation_interior (C.hubBlock_interior s h hn a ha)).trans
      ((G.hubBlock h.val hn).cyclic.rotation a ha) }
  diagram := ((G.hubBlock h.val hn).diagram.adjoinRelation (C.frontierWord s) 0).cast
    (by rw [G.filter_moving_pairing,
      C.filter_cutPairing_interior s _ (C.hubBlock_interior s h hn)]) rfl

noncomputable def sectorHubBlock (s : Bool) (h : C.InteriorHub s)
    (hn : 0 < (P.word (G.hubLabel h.val)).length) : C.SectorBlock s :=
  (C.sectorHubAmbient s h hn).restrict (C.CappedSide s)
    (C.cappedSide_rotation_iff s) (C.cappedSide_pairing_iff s)
    (fun a ha => C.interior_cappedSide (C.hubBlock_interior s h hn a ha))

theorem sectorHubBlock_labels (s : Bool) (h : C.InteriorHub s)
    (hn : 0 < (P.word (G.hubLabel h.val)).length) :
    (C.sectorHubBlock s h hn).diagram.labels = [some (G.hubLabel h.val)] := by
  exact ((C.sectorHubAmbient s h hn).restrict_labels (C.CappedSide s)
    (C.cappedSide_rotation_iff s) (C.cappedSide_pairing_iff s)
    (fun a ha => C.interior_cappedSide (C.hubBlock_interior s h hn a ha))).trans
      (by simp only [sectorHubAmbient, Diagram.labels_cast, Diagram.labels_adjoinRelation,
        G.hubBlock_labels, List.map_cons, List.map_nil])

theorem sectorHubBlock_mem (s : Bool) (h : C.InteriorHub s)
    (hn : 0 < (P.word (G.hubLabel h.val)).length) (a : C.CappedDart s) :
    a ∈ (C.sectorHubBlock s h hn).ports ↔ ∃ i, Port.hub h.val i = a.val := by
  rw [sectorHubBlock, DiagramBlock.restrict_mem]
  exact G.hubBlock_mem h.val hn a.val

def sectorJointPorts (s : Bool) (j : C.InteriorJoint s) : List G.Dart :=
  [.joint j.val false, .joint j.val true]

theorem mem_sectorJointPorts (s : Bool) (j : C.InteriorJoint s) (a : G.Dart) :
    a ∈ C.sectorJointPorts s j ↔ ∃ b, Port.joint j.val b = a := by
  simp only [sectorJointPorts, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
  · rintro ⟨b, rfl⟩
    cases b <;> simp

theorem jointPorts_interior (s : Bool) (j : C.InteriorJoint s)
    (a : G.Dart) (ha : a ∈ C.sectorJointPorts s j) : C.InteriorVertex s a.vertex := by
  obtain ⟨b, rfl⟩ := (C.mem_sectorJointPorts s j a).mp ha
  exact j.property

theorem sectorJointPorts_cyclic (s : Bool) (j : C.InteriorJoint s) :
    IsCycleWord (C.edgeTwist * G.rotation) (C.sectorJointPorts s j) := by
  refine ⟨by simp [sectorJointPorts], by simp [sectorJointPorts], ?_⟩
  intro a ha
  rw [C.twisted_rotation_interior (C.jointPorts_interior s j a ha)]
  obtain ⟨b, rfl⟩ := (C.mem_sectorJointPorts s j a).mp ha
  cases b <;> simp [sectorJointPorts, G.rotation_joint]

noncomputable def sectorJointAmbient (s : Bool) (j : C.InteriorJoint s) :
    DiagramBlock (P.adjoinRelation (C.frontierWord s) 0) (Port.label G.jointLabel)
      (C.edgeTwist * G.rotation) C.cutPairing where
  ports := C.sectorJointPorts s j
  cyclic := C.sectorJointPorts_cyclic s j
  diagram := (Diagram.cap (P := P.adjoinRelation (C.frontierWord s) 0) (G.jointLabel j.val)).cast
    (by rw [C.filter_cutPairing_interior s _ (C.jointPorts_interior s j)]; rfl) rfl

noncomputable def sectorJointBlock (s : Bool) (j : C.InteriorJoint s) : C.SectorBlock s :=
  (C.sectorJointAmbient s j).restrict (C.CappedSide s)
    (C.cappedSide_rotation_iff s) (C.cappedSide_pairing_iff s)
    (fun a ha => C.interior_cappedSide (C.jointPorts_interior s j a ha))

theorem sectorJointBlock_labels (s : Bool) (j : C.InteriorJoint s) :
    (C.sectorJointBlock s j).diagram.labels = [] := by
  exact ((C.sectorJointAmbient s j).restrict_labels (C.CappedSide s)
    (C.cappedSide_rotation_iff s) (C.cappedSide_pairing_iff s)
    (fun a ha => C.interior_cappedSide (C.jointPorts_interior s j a ha))).trans
      (by simp only [sectorJointAmbient, Diagram.labels_cast, Diagram.labels])

theorem sectorJointBlock_mem (s : Bool) (j : C.InteriorJoint s) (a : C.CappedDart s) :
    a ∈ (C.sectorJointBlock s j).ports ↔ ∃ b, Port.joint j.val b = a.val := by
  rw [sectorJointBlock, DiagramBlock.restrict_mem]
  exact C.mem_sectorJointPorts s j a.val

end PortGraph.SimpleCircuit
end ThomGame.Pictures
