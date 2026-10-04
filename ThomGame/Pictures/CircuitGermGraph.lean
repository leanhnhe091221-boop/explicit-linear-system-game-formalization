module

public import ThomGame.Pictures.CircuitGermPorts

/-!
# A labelled circuit germ as an actual port graph

All circuit vertices and one side's internal vertices are retained in
full. The opposite frontier is the ordered lower boundary. Its new leaf
at each outward port is paired only with that port, not with the other
end of the original edge. Internal labels and rotations are unchanged.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open Equiv RibbonConnectivity
open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {G : PortGraph P [] []} (C : G.SimpleCircuit)
  (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
    2 * Nat.card (Component G.circuitStep G.pairing.perm))

abbrev GermHub (s : Bool) := G.SelectedHub (C.GermVertex s)
abbrev GermJoint (s : Bool) := G.SelectedJoint (C.GermVertex s)

noncomputable instance germHubFintype (s : Bool) : Fintype (C.GermHub s) :=
  inferInstanceAs (Fintype {h : G.Hub // C.GermVertex s (.inr (.inl h))})

noncomputable instance germJointFintype (s : Bool) : Fintype (C.GermJoint s) :=
  inferInstanceAs (Fintype {j : G.Joint // C.GermVertex s (.inr (.inr j))})

abbrev GermPort (s : Bool) :=
  Port P [] (C.frontierWord (!s)) (C.GermHub s) (C.GermJoint s) (fun h => G.hubLabel h.val)

noncomputable def germPorts (s : Bool) : C.GermPort s ≃ C.GermRaw s :=
  (Port.bottomPorts _ _ _ _).trans
    ((Equiv.sumCongr (C.boundaryEnumeration (!s)) (G.selectedPorts (C.GermVertex s))).trans
      ((Equiv.sumCongr (Equiv.refl _) (C.germOriginalEquiv hEuler s)).trans (C.germReorder s)))

include hEuler in
theorem germPorts_bottom (s : Bool) (i : Fin (C.frontierWord (!s)).length) :
    C.germPorts hEuler s (.bottom i) = C.germBoundary s (C.boundaryEnumeration (!s) i) := rfl

include hEuler in
theorem germPorts_hub (s : Bool) (h : C.GermHub s) (i : Fin (P.word (G.hubLabel h.val)).length) :
    C.germPorts hEuler s (.hub h i) =
      C.germOriginal hEuler s ⟨.hub h.val i, h.property⟩ := rfl

include hEuler in
theorem germPorts_joint (s : Bool) (j : C.GermJoint s) (b : Bool) :
    C.germPorts hEuler s (.joint j b) =
      C.germOriginal hEuler s ⟨.joint j.val b, j.property⟩ := rfl

include hEuler in
theorem germPorts_label (s : Bool) (a : C.GermPort s) :
    C.germRawLabel s (C.germPorts hEuler s a) =
      Port.label (fun j : C.GermJoint s => G.jointLabel j.val) a := by
  cases a with
  | top i => exact i.elim0
  | bottom i => exact C.boundaryEnumeration_label (!s) i
  | hub h i => exact C.germOriginal_label hEuler s ⟨.hub h.val i, h.property⟩
  | joint j b => exact C.germOriginal_label hEuler s ⟨.joint j.val b, j.property⟩

@[reducible] noncomputable def germGraph (s : Bool) : PortGraph P [] (C.frontierWord (!s)) where
  Hub := C.GermHub s
  Joint := C.GermJoint s
  hubLabel h := G.hubLabel h.val
  hubFlip h := G.hubFlip h.val
  jointLabel j := G.jointLabel j.val
  pairing := (C.germRawPairing s).transport (C.germPorts hEuler s).symm _ (by
    intro a
    obtain ⟨b, rfl⟩ := (C.germPorts hEuler s).surjective a
    rw [Equiv.symm_apply_apply]
    exact (C.germPorts_label hEuler s b).symm)

include hEuler in
theorem germGraph_twin (s : Bool) (a : (C.germGraph hEuler s).Dart) :
    C.germPorts hEuler s ((C.germGraph hEuler s).pairing.twin a) =
      (C.germRawPairing s).twin (C.germPorts hEuler s a) := by
  simp only [germGraph, Pairing.transport, Equiv.symm_symm, Equiv.apply_symm_apply]

noncomputable def germInternalPort (s : Bool) (a : {a : G.Dart // C.GermVertex s a.vertex}) :
    (C.germGraph hEuler s).Dart := (C.germPorts hEuler s).symm (C.germOriginal hEuler s a)

include hEuler in
theorem germInternalPort_hub (s : Bool) (h : C.GermHub s) (i : Fin (P.word (G.hubLabel h.val)).length) :
    C.germInternalPort hEuler s ⟨.hub h.val i, h.property⟩ = .hub h i :=
  (C.germPorts hEuler s).symm_apply_apply (.hub h i)

include hEuler in
theorem germInternalPort_joint (s : Bool) (j : C.GermJoint s) (b : Bool) :
    C.germInternalPort hEuler s ⟨.joint j.val b, j.property⟩ = .joint j b :=
  (C.germPorts hEuler s).symm_apply_apply (.joint j b)

include hEuler in
theorem germGraph_twin_internal_uncut (s : Bool) (a : {a : G.Dart // C.GermVertex s a.vertex})
    (ha : C.UncutDart s a.val) :
    (C.germGraph hEuler s).pairing.twin (C.germInternalPort hEuler s a) =
      C.germInternalPort hEuler s ⟨G.pairing.twin a.val,
        (C.germ_vertex_port_iff hEuler s _).mpr (Or.inl ((C.uncutDart_twin_iff s _).mpr ha))⟩ := by
  apply (C.germPorts hEuler s).injective
  rw [C.germGraph_twin]
  change (C.germRawPairing s).twin
    (C.germPorts hEuler s ((C.germPorts hEuler s).symm (C.germOriginal hEuler s a))) = _
  rw [Equiv.apply_symm_apply]
  simpa only [germInternalPort, Equiv.apply_symm_apply] using
    C.germRaw_twin_original_uncut hEuler s a ha

include hEuler in
theorem germGraph_twin_internal_outward (s : Bool) (a : {a : G.Dart // C.GermVertex s a.vertex})
    (ha : C.Frontier (!s) a.val) :
    (C.germGraph hEuler s).pairing.twin (C.germInternalPort hEuler s a) =
      .bottom ((C.boundaryEnumeration (!s)).symm ⟨a.val, ha⟩) := by
  apply (C.germPorts hEuler s).injective
  rw [C.germGraph_twin, C.germPorts_bottom]
  change (C.germRawPairing s).twin
    (C.germPorts hEuler s ((C.germPorts hEuler s).symm (C.germOriginal hEuler s a))) = _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact C.germRaw_twin_original_outward hEuler s a ha

include hEuler in
theorem germGraph_twin_bottom (s : Bool) (i : Fin (C.frontierWord (!s)).length) :
    (C.germGraph hEuler s).pairing.twin (.bottom i) =
      C.germInternalPort hEuler s ⟨(C.boundaryEnumeration (!s) i).val,
        (C.germ_vertex_port_iff hEuler s _).mpr (Or.inr (C.boundaryEnumeration (!s) i).property)⟩ := by
  apply (C.germPorts hEuler s).injective
  rw [C.germGraph_twin, C.germPorts_bottom]
  simpa only [germInternalPort, Equiv.apply_symm_apply] using
    C.germRaw_twin_boundary hEuler s (C.boundaryEnumeration (!s) i)

include hEuler in
theorem germGraph_hub_rotation (s : Bool) (h : C.GermHub s) (i : Fin (P.word (G.hubLabel h.val)).length) :
    (C.germGraph hEuler s).rotation (.hub h i) = .hub h (G.hubRotation h.val i) := rfl

include hEuler in
theorem germGraph_joint_rotation (s : Bool) (j : C.GermJoint s) (b : Bool) :
    (C.germGraph hEuler s).rotation (.joint j b) = .joint j (!b) := rfl

end ThomGame.Pictures.PortGraph.SimpleCircuit
