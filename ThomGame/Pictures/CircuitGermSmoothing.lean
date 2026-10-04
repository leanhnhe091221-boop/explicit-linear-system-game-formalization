module

public import ThomGame.Pictures.CircuitGermGluing
public import ThomGame.Pictures.SelectedSmoothingTrace
public import ThomGame.Pictures.ReturnTransport

/-!
# An actual smoothing certificate for the germ-region composition

Only the newly created seam joints are removed. Every seam wire reaches
an old port, so the trace loses no circles. Its final ports correspond
bijectively to the original circuit component and recover its exact
edge pairing. This is still a graph statement, not a diagram realization.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open Equiv MarkedReturn
open scoped BigOperators Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {G : PortGraph P [] []} (C : G.SimpleCircuit)
  (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
    2 * Nat.card (RibbonConnectivity.Component G.circuitStep G.pairing.perm))

def GluedSeam (s : Bool) : (C.gluedGraph hEuler s).Joint → Prop
  | .inl _ => False
  | .inr _ => True

include hEuler in
theorem glued_selectedTurn (s : Bool) (a : (C.gluedGraph hEuler s).Dart) :
    (C.gluedGraph hEuler s).selectedTurn (C.GluedSeam hEuler s) a = C.gluedSeamTurn hEuler s a := by
  cases a with
  | top i => exact i.elim0
  | bottom i => exact i.elim0
  | hub h i => rfl
  | joint j b => cases j <;> simp [selectedTurn, GluedSeam, gluedSeamTurn]

include hEuler in
theorem glued_selectedStep (s : Bool) :
    (C.gluedGraph hEuler s).selectedStep (C.GluedSeam hEuler s) = C.gluedStep hEuler s := by
  ext a
  exact C.glued_selectedTurn hEuler s ((C.gluedGraph hEuler s).pairing.twin a)

include hEuler in
theorem glued_selectedTerminal (s : Bool) (a : (C.gluedGraph hEuler s).Dart) :
    (C.gluedGraph hEuler s).SelectedTerminal (C.GluedSeam hEuler s) a ↔ C.GluedRetained hEuler s a := by
  rw [C.gluedRetained_iff]
  cases a with
  | top i => exact i.elim0
  | bottom i => exact i.elim0
  | hub h i => rfl
  | joint j b => cases j <;> simp [SelectedTerminal, GluedSeam]

include hEuler in
theorem gluing_accessible (s : Bool) (a : C.GluingRaw s) :
    ∃ b : C.GluingRaw s, C.GluingRetained s b ∧ (C.gluingStep hEuler s).SameCycle a b := by
  rcases a with (a | ⟨a, b⟩) | a
  · exact ⟨.inl (.inl a), trivial, Equiv.Perm.SameCycle.rfl⟩
  · cases b
    · exact ⟨.inl (.inr (a, false)), rfl, Equiv.Perm.SameCycle.rfl⟩
    · refine ⟨.inl (.inr (a, false)), rfl, ?_⟩
      exact (MarkedReturn.Hit.direct (f := C.gluingStep hEuler s) (p := C.GluingRetained s)
        (.inl (.inr (a, true)))).sameCycle
  · exact ⟨C.gluingOriginalPort s (.inr ((C.keptPairing (!s)).twin a)),
      C.gluingOriginalPort_retained s _, (C.gluing_region_hit hEuler s a).sameCycle⟩

include hEuler in
theorem glued_selectedAccessible (s : Bool) :
    (C.gluedGraph hEuler s).SelectedAccessible (C.GluedSeam hEuler s) := by
  intro a
  obtain ⟨b, hb, hab⟩ := C.gluing_accessible hEuler s (C.gluedPorts hEuler s a)
  refine ⟨(C.gluedPorts hEuler s).symm b, ?_, ?_⟩
  · apply (C.glued_selectedTerminal hEuler s _).mpr
    change C.GluingRetained s (C.gluedPorts hEuler s ((C.gluedPorts hEuler s).symm b))
    rwa [Equiv.apply_symm_apply]
  · rw [C.glued_selectedStep]
    apply (FiniteReturn.sameCycle_congr (C.gluedStep hEuler s) (C.gluingStep hEuler s)
      (C.gluedPorts hEuler s) (fun x => (C.gluedPorts_step hEuler s x).symm) _ _).mpr
    rwa [Equiv.apply_symm_apply]

noncomputable def gluedRetainedPortEquiv (s : Bool) :
    C.GluingOriginal s ≃ Subtype (C.GluedRetained hEuler s) :=
  (C.gluingRetainedEquiv hEuler s).trans
    ((C.gluedPorts hEuler s).subtypeEquiv (fun _ => Iff.rfl)).symm

include hEuler in
theorem glued_firstReturn_component (s : Bool) (a : Subtype (C.GluedRetained hEuler s)) :
    (C.gluedComponentPorts hEuler s
      (MarkedReturn.perm (C.gluedStep hEuler s) (C.GluedRetained hEuler s) a)).val =
        G.pairing.twin (C.gluedComponentPorts hEuler s a).val := by
  obtain ⟨b, rfl⟩ := (C.gluedRetainedPortEquiv hEuler s).surjective a
  rw [C.gluedComponentPorts_val]
  change C.gluingRawVal s (C.gluedPorts hEuler s
    (MarkedReturn.perm (C.gluedStep hEuler s) (C.GluedRetained hEuler s)
      ⟨C.gluedOriginalPort hEuler s b, _⟩).val) = _
  rw [C.glued_firstReturn_val, C.gluedComponentPorts_val]
  change G.pairing.twin (C.gluingOriginalVal s b) =
    G.pairing.twin (C.gluingRawVal s (C.gluedPorts hEuler s
      ((C.gluedPorts hEuler s).symm (C.gluingOriginalPort s b))))
  rw [Equiv.apply_symm_apply, C.gluingOriginalPort_val]

/-- The certified finite reduction deletes exactly the newly added seam joints. -/
noncomputable def germReduction (s : Bool) :
    SelectedReduction (C.gluedGraph hEuler s) (C.GluedSeam hEuler s) :=
  (C.gluedGraph hEuler s).reduceSelected (C.GluedSeam hEuler s) (C.glued_selectedAccessible hEuler s)

noncomputable def recoveredPorts (s : Bool) :
    (C.germReduction hEuler s).graph.Dart ≃ {a : G.Dart //
      RibbonConnectivity.Connected G.circuitStep G.pairing.perm a C.cutBase} :=
  ((C.germReduction hEuler s).trace.selectedTerminalEquiv _
    (C.germReduction hEuler s).removesOnly (C.germReduction hEuler s).clearsSelected).trans
    ((Equiv.subtypeEquivRight (C.glued_selectedTerminal hEuler s)).trans (C.gluedComponentPorts hEuler s))

include hEuler in
theorem germReduction_return (s : Bool) (a : (C.germReduction hEuler s).graph.Dart) :
    (C.germReduction hEuler s).trace.portEmbedding ((C.germReduction hEuler s).graph.pairing.twin a) =
      (MarkedReturn.perm (C.gluedStep hEuler s) (C.GluedRetained hEuler s)
        ⟨(C.germReduction hEuler s).trace.portEmbedding a,
          (C.glued_selectedTerminal hEuler s _).mp
            (((C.germReduction hEuler s).trace.selectedTerminalEquiv _
              (C.germReduction hEuler s).removesOnly (C.germReduction hEuler s).clearsSelected) a).property⟩).val := by
  have hr := (C.germReduction hEuler s).trace.selected_twin_return _
    (C.germReduction hEuler s).removesOnly (C.germReduction hEuler s).clearsSelected a
  rw [C.glued_selectedStep] at hr
  exact hr.trans (MarkedReturn.perm_eq_of_pred_iff (C.gluedStep hEuler s) _ _
    (C.glued_selectedTerminal hEuler s) _)

include hEuler in
theorem recoveredPorts_twin (s : Bool) (a : (C.germReduction hEuler s).graph.Dart) :
    (C.recoveredPorts hEuler s ((C.germReduction hEuler s).graph.pairing.twin a)).val =
      G.pairing.twin (C.recoveredPorts hEuler s a).val := by
  let x : Subtype (C.GluedRetained hEuler s) :=
    Equiv.subtypeEquivRight (C.glued_selectedTerminal hEuler s)
      (((C.germReduction hEuler s).trace.selectedTerminalEquiv _
        (C.germReduction hEuler s).removesOnly (C.germReduction hEuler s).clearsSelected) a)
  have he : (Equiv.subtypeEquivRight (C.glued_selectedTerminal hEuler s)
      (((C.germReduction hEuler s).trace.selectedTerminalEquiv _
        (C.germReduction hEuler s).removesOnly (C.germReduction hEuler s).clearsSelected)
          ((C.germReduction hEuler s).graph.pairing.twin a))) =
      MarkedReturn.perm (C.gluedStep hEuler s) (C.GluedRetained hEuler s) x :=
    Subtype.ext (C.germReduction_return hEuler s a)
  change (C.gluedComponentPorts hEuler s _).val = G.pairing.twin (C.gluedComponentPorts hEuler s x).val
  rw [he]
  exact C.glued_firstReturn_component hEuler s x

include hEuler in
theorem germReduction_sign (s : Bool) :
    (C.germReduction hEuler s).graph.sign = ∑ h : C.ComponentHub, P.parity (G.hubLabel h.val) :=
  (C.germReduction hEuler s).trace.sign.trans (C.gluedGraph_sign hEuler s)

include hEuler in
theorem germReduction_character [DecidableEq R] (s : Bool) (r : R) :
    (C.germReduction hEuler s).graph.character r =
      ∑ h : C.ComponentHub, if G.hubLabel h.val = r then (1 : ZMod 2) else 0 :=
  ((C.germReduction hEuler s).trace.character r).trans (C.gluedGraph_character hEuler s r)

end ThomGame.Pictures.PortGraph.SimpleCircuit
