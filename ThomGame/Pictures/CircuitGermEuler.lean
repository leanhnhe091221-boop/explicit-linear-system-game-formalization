module

public import ThomGame.Pictures.CircuitGermPartialEuler
public import ThomGame.Pictures.LeafCompletionEuler

/-!
# Euler saturation of the actual circuit germ

The fixed ports of the partial germ pairing are exactly the outward
frontier. Completing them by leaves gives the existing germ graph by an
explicit equivalence preserving both rotation and pairing. Consequently
the actual germ graph, with its existing indexed boundary, is saturated.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open Equiv RibbonConnectivity
open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {G : PortGraph P [] []}
    (C : G.SimpleCircuit)
    (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
      2 * Nat.card (Component G.circuitStep G.pairing.perm))

include hEuler in
theorem germPartialPairing_fixed_iff (s : Bool) (a : C.GermOriginalPort s) :
    C.germPartialPairing hEuler s a = a ↔ C.Frontier (!s) a.val := by
  constructor
  · intro he
    have hn : ¬ C.UncutDart s a.val := by
      intro ha
      have hv := congrArg Subtype.val he
      rw [C.germPartialPairing_val, ite_eq_left ha] at hv
      exact G.pairing.ne_self a.val hv
    exact ((C.germ_vertex_port_iff hEuler s a.val).mp a.property).resolve_left hn
  · intro ha
    have hn : ¬ C.UncutDart s a.val := fun hu => C.uncut_not_outward hEuler hu ha
    apply Subtype.ext
    rw [C.germPartialPairing_val, ite_eq_right hn]

noncomputable def germFixedEquiv (s : Bool) :
    LeafCompletion.Fixed (C.germPartialPairing hEuler s) ≃ Subtype (C.Frontier (!s)) where
  toFun a := ⟨a.val.val, (C.germPartialPairing_fixed_iff hEuler s a.val).mp a.property⟩
  invFun a :=
    ⟨⟨a.val, (C.germ_vertex_port_iff hEuler s a.val).mpr (Or.inr a.property)⟩,
      (C.germPartialPairing_fixed_iff hEuler s _).mpr a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def germPortSplit (s : Bool) :
    C.GermPort s ≃ Subtype (C.Frontier (!s)) ⊕ C.GermOriginalPort s :=
  (Port.bottomPorts _ _ _ _).trans
    (Equiv.sumCongr (C.boundaryEnumeration (!s)) (G.selectedPorts (C.GermVertex s)))

theorem germPortSplit_bottom (s : Bool) (i : Fin (C.frontierWord (!s)).length) :
    C.germPortSplit s (.bottom i) = .inl (C.boundaryEnumeration (!s) i) := rfl

include hEuler in
theorem germPortSplit_internal (s : Bool) (a : C.GermOriginalPort s) :
    C.germPortSplit s (C.germInternalPort hEuler s a) = .inr a := by
  rcases a with ⟨a, ha⟩
  cases a with
  | top i => exact i.elim0
  | bottom i => exact i.elim0
  | hub h i => rw [C.germInternalPort_hub hEuler s ⟨h, ha⟩]; rfl
  | joint j b => rw [C.germInternalPort_joint hEuler s ⟨j, ha⟩]; rfl

noncomputable def germCompletionPorts (s : Bool) :
    LeafCompletion.Dart (C.germPartialPairing hEuler s) ≃ (C.germGraph hEuler s).Dart :=
  ((Equiv.sumCongr (Equiv.refl _) (C.germFixedEquiv hEuler s)).trans
    (Equiv.sumComm _ _)).trans (C.germPortSplit s).symm

include hEuler in
theorem germCompletionPorts_inl (s : Bool) (a : C.GermOriginalPort s) :
    C.germCompletionPorts hEuler s (.inl a) = C.germInternalPort hEuler s a := by
  apply (C.germPortSplit s).injective
  rw [C.germPortSplit_internal]
  exact (C.germPortSplit s).apply_symm_apply (.inr a)

include hEuler in
theorem germCompletionPorts_inr (s : Bool)
    (a : LeafCompletion.Fixed (C.germPartialPairing hEuler s)) :
    C.germCompletionPorts hEuler s (.inr a) =
      .bottom ((C.boundaryEnumeration (!s)).symm (C.germFixedEquiv hEuler s a)) := by
  apply (C.germPortSplit s).injective
  rw [C.germPortSplit_bottom, Equiv.apply_symm_apply]
  exact (C.germPortSplit s).apply_symm_apply (.inl (C.germFixedEquiv hEuler s a))

include hEuler in
theorem germCompletionPorts_rotation (s : Bool)
    (a : LeafCompletion.Dart (C.germPartialPairing hEuler s)) :
    (C.germGraph hEuler s).rotation (C.germCompletionPorts hEuler s a) =
      C.germCompletionPorts hEuler s
        (LeafCompletion.rotation (C.germPartialRotation s) (C.germPartialPairing hEuler s) a) := by
  rcases a with a | a
  · rw [LeafCompletion.rotation_inl, C.germCompletionPorts_inl, C.germCompletionPorts_inl,
      C.germInternalPort_rotation]
    rfl
  · rw [LeafCompletion.rotation_inr, C.germCompletionPorts_inr]
    rfl

include hEuler in
theorem germCompletionPorts_pairing (s : Bool)
    (a : LeafCompletion.Dart (C.germPartialPairing hEuler s)) :
    (C.germGraph hEuler s).pairing.perm (C.germCompletionPorts hEuler s a) =
      C.germCompletionPorts hEuler s
        (LeafCompletion.pairing (C.germPartialPairing hEuler s)
          (C.germPartialPairing_involutive hEuler s) a) := by
  rcases a with a | a
  · by_cases ha : C.Frontier (!s) a.val
    · have hf := (C.germPartialPairing_fixed_iff hEuler s a).mpr ha
      rw [LeafCompletion.pairing_inl_fixed _ _ ⟨a, hf⟩,
        C.germCompletionPorts_inl, C.germCompletionPorts_inr]
      exact C.germGraph_twin_internal_outward hEuler s a ha
    · have hf : C.germPartialPairing hEuler s a ≠ a :=
        fun h => ha ((C.germPartialPairing_fixed_iff hEuler s a).mp h)
      have hu := ((C.germ_vertex_port_iff hEuler s a.val).mp a.property).resolve_right ha
      rw [LeafCompletion.pairing_inl_moving _ _ hf, C.germCompletionPorts_inl, C.germCompletionPorts_inl]
      change (C.germGraph hEuler s).pairing.twin (C.germInternalPort hEuler s a) = _
      rw [C.germGraph_twin_internal_uncut hEuler s a hu]
      apply congrArg (C.germInternalPort hEuler s)
      apply Subtype.ext
      rw [C.germPartialPairing_val, ite_eq_left hu]
  · rw [LeafCompletion.pairing_inr, C.germCompletionPorts_inl, C.germCompletionPorts_inr]
    change (C.germGraph hEuler s).pairing.twin (.bottom _) = _
    rw [C.germGraph_twin_bottom]
    apply congrArg (C.germInternalPort hEuler s)
    apply Subtype.ext
    rw [Equiv.apply_symm_apply]
    rfl

include hEuler in
theorem germGraph_rotationEuler (s : Bool) :
    RotationEuler.count (C.germGraph hEuler s).rotation (C.germGraph hEuler s).pairing.perm =
      2 * Nat.card (Component (C.germGraph hEuler s).rotation (C.germGraph hEuler s).pairing.perm) := by
  have hs := LeafCompletion.saturated (C.germPartialRotation s) (C.germPartialPairing hEuler s)
    (C.germPartialPairing_involutive hEuler s) (C.germPartial_saturated hEuler s)
  rw [RotationEuler.count_congr _ _ (C.germGraph hEuler s).rotation
      (C.germGraph hEuler s).pairing.perm (C.germCompletionPorts hEuler s)
      (C.germCompletionPorts_rotation hEuler s) (C.germCompletionPorts_pairing hEuler s),
    Nat.card_congr (componentCongrEquiv _ _ (C.germGraph hEuler s).rotation
      (C.germGraph hEuler s).pairing.perm (C.germCompletionPorts hEuler s)
      (C.germCompletionPorts_rotation hEuler s) (C.germCompletionPorts_pairing hEuler s))] at hs
  exact hs

end ThomGame.Pictures.PortGraph.SimpleCircuit
