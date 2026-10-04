module

public import ThomGame.Pictures.CircuitGermReturn
public import ThomGame.Pictures.CircuitGermCharge

/-!
# Gluing the actual germ and region port graphs

The composition has one new degree-two seam vertex per outward port.
Its edge pairing and the turn at just those vertices agree with the raw
first-return model. Thus bypassing the seams recovers every original
edge endpoint in the original circuit component.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open Equiv MarkedReturn
open scoped BigOperators Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {G : PortGraph P [] []} (C : G.SimpleCircuit)
  (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
    2 * Nat.card (RibbonConnectivity.Component G.circuitStep G.pairing.perm))

@[reducible] noncomputable def gluedGraph (s : Bool) : PortGraph P [] [] :=
  (C.germGraph hEuler s).comp (C.regionGraph hEuler (!s))

noncomputable def gluedPorts (s : Bool) : (C.gluedGraph hEuler s).Dart ≃ C.GluingRaw s :=
  (compPorts (C.germGraph hEuler s) (C.regionGraph hEuler (!s))).symm.trans
    (Equiv.sumCongr (C.germPorts hEuler s) (C.regionPorts hEuler (!s)))

include hEuler in
theorem gluedPorts_comp (s : Bool)
    (a : (C.germGraph hEuler s).Dart ⊕ (C.regionGraph hEuler (!s)).Dart) :
    C.gluedPorts hEuler s (compPorts (C.germGraph hEuler s) (C.regionGraph hEuler (!s)) a) =
      Equiv.sumCongr (C.germPorts hEuler s) (C.regionPorts hEuler (!s)) a :=
  congrArg (Equiv.sumCongr (C.germPorts hEuler s) (C.regionPorts hEuler (!s)))
    ((compPorts (C.germGraph hEuler s) (C.regionGraph hEuler (!s))).symm_apply_apply a)

include hEuler in
theorem gluedPorts_twin (s : Bool) (a : (C.gluedGraph hEuler s).Dart) :
    C.gluedPorts hEuler s ((C.gluedGraph hEuler s).pairing.twin a) =
      (C.gluingRawPairing s).twin (C.gluedPorts hEuler s a) := by
  obtain ⟨b, rfl⟩ := (compPorts (C.germGraph hEuler s) (C.regionGraph hEuler (!s))).surjective a
  rw [twin_compPorts, C.gluedPorts_comp, C.gluedPorts_comp]
  rcases b with b | b
  · change Sum.inl (C.germPorts hEuler s ((C.germGraph hEuler s).pairing.twin b)) =
      Sum.inl ((C.germRawPairing s).twin (C.germPorts hEuler s b))
    exact congrArg Sum.inl (C.germGraph_twin hEuler s b)
  · change Sum.inr (C.regionPorts hEuler (!s) ((C.regionGraph hEuler (!s)).pairing.twin b)) =
      Sum.inr ((C.keptPairing (!s)).twin (C.regionPorts hEuler (!s) b))
    exact congrArg Sum.inr (Subtype.ext (C.regionGraph_twin hEuler (!s) b))

/-- Turn at new composition junctions, leaving all original vertices fixed. -/
def gluedSeamTurn (s : Bool) : (C.gluedGraph hEuler s).Dart → (C.gluedGraph hEuler s).Dart
  | .joint (.inr i) b => .joint (.inr i) (!b)
  | a => a

include hEuler in
theorem gluedSeamTurn_involutive (s : Bool) : Function.Involutive (C.gluedSeamTurn hEuler s) := by
  intro a
  cases a with
  | top i => exact i.elim0
  | bottom i => exact i.elim0
  | hub h i => rfl
  | joint j b => cases j <;> simp [gluedSeamTurn]

noncomputable def gluedSeamPerm (s : Bool) : Equiv.Perm (C.gluedGraph hEuler s).Dart :=
  ⟨C.gluedSeamTurn hEuler s, C.gluedSeamTurn hEuler s,
    C.gluedSeamTurn_involutive hEuler s, C.gluedSeamTurn_involutive hEuler s⟩

include hEuler in
theorem gluingSeamTurn_germOriginal (s : Bool) (a : {a : G.Dart // C.GermVertex s a.vertex}) :
    C.gluingSeamTurn hEuler s (.inl (C.germOriginal hEuler s a)) =
      .inl (C.germOriginal hEuler s a) := by
  rcases (C.germ_vertex_port_iff hEuler s a.val).mp a.property with hu | hf
  · rw [C.germOriginal_of_uncut hEuler s a hu]
    rfl
  · rw [C.germOriginal_of_outward hEuler s a hf]
    rfl

include hEuler in
theorem gluedPorts_seam (s : Bool) (a : (C.gluedGraph hEuler s).Dart) :
    C.gluedPorts hEuler s (C.gluedSeamTurn hEuler s a) =
      C.gluingSeamTurn hEuler s (C.gluedPorts hEuler s a) := by
  cases a with
  | top i => exact i.elim0
  | bottom i => exact i.elim0
  | hub h i =>
    rcases h with h | h
    · exact (C.gluingSeamTurn_germOriginal hEuler s ⟨.hub h.val i, h.property⟩).symm
    · have hn : ¬ C.Frontier (!s) (Port.hub h.val i : G.Dart) :=
        fun hf => h.property.1 ((C.frontier_iff hEuler (!s) _).mp hf).1
      change Sum.inr _ = C.gluingSeamTurn hEuler s (.inr (C.regionPorts hEuler (!s) (.hub h i)))
      symm
      exact dite_eq_right hn
  | joint j b =>
    rcases j with (j | j) | i
    · exact (C.gluingSeamTurn_germOriginal hEuler s ⟨.joint j.val b, j.property⟩).symm
    · have hn : ¬ C.Frontier (!s) (Port.joint j.val b : G.Dart) :=
        fun hf => j.property.1 ((C.frontier_iff hEuler (!s) _).mp hf).1
      change Sum.inr _ = C.gluingSeamTurn hEuler s (.inr (C.regionPorts hEuler (!s) (.joint j b)))
      symm
      exact dite_eq_right hn
    · cases b
      · rfl
      · change Sum.inl (C.germBoundary s (C.boundaryEnumeration (!s) i)) =
          C.gluingSeamTurn hEuler s (.inr (C.frontierKept hEuler s (C.boundaryEnumeration (!s) i)))
        simp [gluingSeamTurn, frontierKept, (C.boundaryEnumeration (!s) i).property, germBoundary]

noncomputable def gluedStep (s : Bool) : Equiv.Perm (C.gluedGraph hEuler s).Dart :=
  C.gluedSeamPerm hEuler s * (C.gluedGraph hEuler s).pairing.perm

include hEuler in
theorem gluedPorts_step (s : Bool) (a : (C.gluedGraph hEuler s).Dart) :
    C.gluedPorts hEuler s (C.gluedStep hEuler s a) =
      C.gluingStep hEuler s (C.gluedPorts hEuler s a) := by
  change C.gluedPorts hEuler s (C.gluedSeamTurn hEuler s ((C.gluedGraph hEuler s).pairing.twin a)) = _
  rw [C.gluedPorts_seam, C.gluedPorts_twin]
  rfl

def GluedRetained (s : Bool) (a : (C.gluedGraph hEuler s).Dart) : Prop :=
  C.GluingRetained s (C.gluedPorts hEuler s a)

include hEuler in
/-- Precisely the old ports are retained: only new seam ports are skipped. -/
theorem gluedRetained_iff (s : Bool) (a : (C.gluedGraph hEuler s).Dart) :
    C.GluedRetained hEuler s a ↔ (match a with | .joint (.inr _) _ => False | _ => True) := by
  change C.GluingRetained s (C.gluedPorts hEuler s a) ↔ _
  rw [C.gluingRetained_iff_fixed hEuler, ← C.gluedPorts_seam hEuler,
    (C.gluedPorts hEuler s).injective.eq_iff]
  cases a with
  | top i => exact i.elim0
  | bottom i => exact i.elim0
  | hub h i => simp [gluedSeamTurn]
  | joint j b =>
    cases j
    · simp [gluedSeamTurn]
    · cases b <;> constructor <;> intro h <;> cases h

/-- All old component ports, each exactly once, after discarding only seam ports. -/
noncomputable def gluedComponentPorts (s : Bool) :
    Subtype (C.GluedRetained hEuler s) ≃ {a : G.Dart //
      RibbonConnectivity.Connected G.circuitStep G.pairing.perm a C.cutBase} :=
  ((C.gluedPorts hEuler s).subtypeEquiv (fun _ => Iff.rfl)).trans
    ((C.gluingRetainedEquiv hEuler s).symm.trans (C.gluingComponentEquiv hEuler s))

include hEuler in
theorem gluedComponentPorts_val (s : Bool) (a : Subtype (C.GluedRetained hEuler s)) :
    (C.gluedComponentPorts hEuler s a).val = C.gluingRawVal s (C.gluedPorts hEuler s a.val) := by
  change (C.gluingComponentEquiv hEuler s
    ((C.gluingRetainedEquiv hEuler s).symm ⟨C.gluedPorts hEuler s a.val, a.property⟩)).val = _
  rw [C.gluingComponentEquiv_val, C.gluingRetainedEquiv_symm_val]

noncomputable def gluedOriginalPort (s : Bool) (a : C.GluingOriginal s) :
    (C.gluedGraph hEuler s).Dart :=
  (C.gluedPorts hEuler s).symm (C.gluingOriginalPort s a)

include hEuler in
theorem gluedOriginalPort_retained (s : Bool) (a : C.GluingOriginal s) :
    C.GluedRetained hEuler s (C.gluedOriginalPort hEuler s a) := by
  unfold GluedRetained gluedOriginalPort
  rw [Equiv.apply_symm_apply]
  exact C.gluingOriginalPort_retained s a

include hEuler in
theorem glued_original_hit (s : Bool) (a : C.GluingOriginal s) :
    Hit (C.gluedStep hEuler s) (C.GluedRetained hEuler s) (C.gluedOriginalPort hEuler s a)
      (C.gluedOriginalPort hEuler s ((C.gluingOriginalPairing s).twin a)) := by
  apply (C.gluing_original_hit hEuler s a).map (C.gluedPorts hEuler s).symm
  · intro x
    apply (C.gluedPorts hEuler s).injective
    rw [C.gluedPorts_step, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  · intro x
    simp only [GluedRetained, Equiv.apply_symm_apply]

include hEuler in
theorem glued_firstReturn (s : Bool) (a : C.GluingOriginal s) :
    (MarkedReturn.perm (C.gluedStep hEuler s) (C.GluedRetained hEuler s)
      ⟨C.gluedOriginalPort hEuler s a, C.gluedOriginalPort_retained hEuler s a⟩).val =
        C.gluedOriginalPort hEuler s ((C.gluingOriginalPairing s).twin a) :=
  (MarkedReturn.eq_perm_of_hit _ _ _ (C.gluedOriginalPort_retained hEuler s _)
    (C.glued_original_hit hEuler s a)).symm

include hEuler in
theorem glued_firstReturn_val (s : Bool) (a : C.GluingOriginal s) :
    C.gluingRawVal s (C.gluedPorts hEuler s
      (MarkedReturn.perm (C.gluedStep hEuler s) (C.GluedRetained hEuler s)
        ⟨C.gluedOriginalPort hEuler s a, C.gluedOriginalPort_retained hEuler s a⟩).val) =
          G.pairing.twin (C.gluingOriginalVal s a) := by
  rw [C.glued_firstReturn]
  change C.gluingRawVal s ((C.gluedPorts hEuler s)
    ((C.gluedPorts hEuler s).symm (C.gluingOriginalPort s ((C.gluingOriginalPairing s).twin a)))) = _
  rw [Equiv.apply_symm_apply, C.gluingOriginalPort_val, C.gluingOriginal_twin_val]

include hEuler in
theorem gluedGraph_sign (s : Bool) :
    (C.gluedGraph hEuler s).sign = ∑ h : C.ComponentHub, P.parity (G.hubLabel h.val) := by
  rw [gluedGraph, PortGraph.sign_comp]
  exact C.germGraph_region_sign hEuler s

include hEuler in
theorem gluedGraph_character [DecidableEq R] (s : Bool) (r : R) :
    (C.gluedGraph hEuler s).character r =
      ∑ h : C.ComponentHub, if G.hubLabel h.val = r then (1 : ZMod 2) else 0 := by
  rw [PortGraph.character_eq_sum]
  change (∑ h : C.GermHub s ⊕ C.InteriorHub (!s),
    if Sum.elim (fun h : C.GermHub s => G.hubLabel h.val)
      (fun h : C.InteriorHub (!s) => G.hubLabel h.val) h = r then (1 : ZMod 2) else 0) = _
  rw [Fintype.sum_sum_type]
  exact C.germ_region_hub_sum hEuler s (fun h => if G.hubLabel h = r then (1 : ZMod 2) else 0)

end ThomGame.Pictures.PortGraph.SimpleCircuit
