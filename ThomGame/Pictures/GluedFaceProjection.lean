module

public import ThomGame.Pictures.CircuitGermRecovery
public import ThomGame.Pictures.CycleGermFacialSupport
public import ThomGame.Pictures.ReverseComposition
public import ThomGame.Pictures.CircuitCompositionFaces

/-!
# The directed face projection of a germ-region subdivision

The two ports of a new seam project to opposite original darts. This
projection preserves edge reversal exactly. Each face step projects to
one original face step or to a stationary subdivision step.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open RibbonConnectivity

variable {R S : Type*} {P : InvolutionPresentation R S} {G : PortGraph P [] []}
  (C : G.SimpleCircuit)
  (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
    2 * Nat.card (Component G.circuitStep G.pairing.perm))

def gluingFaceVal (s : Bool) : C.GluingRaw s → G.Dart
  | .inl (.inl a) => a.val
  | .inl (.inr (a, false)) => a.val
  | .inl (.inr (a, true)) => G.pairing.twin a.val
  | .inr a => a.val

theorem gluingFaceVal_pairing (s : Bool) (x : C.GluingRaw s) :
    C.gluingFaceVal s ((C.gluingRawPairing s).twin x) = G.pairing.twin (C.gluingFaceVal s x) := by
  rcases x with (x | ⟨x, b⟩) | x
  · rfl
  · cases b
    · rfl
    · exact (G.pairing.involutive x.val).symm
  · rfl

theorem gluingFaceVal_retained (s : Bool) (x : C.GluingRaw s) (hx : C.GluingRetained s x) :
    C.gluingFaceVal s x = C.gluingRawVal s x := by
  rcases x with (x | ⟨x, b⟩) | x
  · rfl
  · change b = false at hx
    subst b
    rfl
  · rfl

noncomputable def gluedFaceProjection (s : Bool) (x : (C.gluedGraph hEuler s).Dart) : G.Dart :=
  C.gluingFaceVal s (C.gluedPorts hEuler s x)

theorem gluedFaceProjection_pairing (s : Bool) (x : (C.gluedGraph hEuler s).Dart) :
    C.gluedFaceProjection hEuler s ((C.gluedGraph hEuler s).pairing.twin x) =
      G.pairing.twin (C.gluedFaceProjection hEuler s x) := by
  unfold gluedFaceProjection
  rw [C.gluedPorts_twin, C.gluingFaceVal_pairing]

theorem gluedFaceProjection_retained (s : Bool) (x : (C.gluedGraph hEuler s).Dart)
    (hx : C.GluedRetained hEuler s x) :
    C.gluedFaceProjection hEuler s x = C.gluedProjection hEuler s x :=
  C.gluingFaceVal_retained s (C.gluedPorts hEuler s x) hx

theorem gluedFaceProjection_seam_false (s : Bool) (i : Fin (C.frontierWord (!s)).length) :
    C.gluedFaceProjection hEuler s (.joint (.inr i) false) =
      G.pairing.twin (C.boundaryEnumeration (!s) i).val := rfl

theorem gluedFaceProjection_seam_true (s : Bool) (i : Fin (C.frontierWord (!s)).length) :
    C.gluedFaceProjection hEuler s (.joint (.inr i) true) = (C.boundaryEnumeration (!s) i).val := rfl

theorem gluedRetained_rotation (s : Bool) (x : (C.gluedGraph hEuler s).Dart) :
    C.GluedRetained hEuler s ((C.gluedGraph hEuler s).rotation x) ↔ C.GluedRetained hEuler s x := by
  rw [C.gluedRetained_iff, C.gluedRetained_iff]
  cases x with
  | top i => exact i.elim0
  | bottom i => exact i.elim0
  | hub h i => rfl
  | joint j b => cases j <;> rfl

theorem gluedFaceProjection_rotation_retained (s : Bool) (x : (C.gluedGraph hEuler s).Dart)
    (hx : C.GluedRetained hEuler s x) :
    C.gluedFaceProjection hEuler s ((C.gluedGraph hEuler s).rotation x) =
      G.rotation (C.gluedFaceProjection hEuler s x) := by
  rw [C.gluedFaceProjection_retained hEuler s _ ((C.gluedRetained_rotation hEuler s x).mpr hx),
    C.gluedFaceProjection_retained hEuler s x hx, C.gluedProjection_rotation hEuler s x hx]

theorem gluedFaceProjection_rotation (s : Bool) (x : (C.gluedGraph hEuler s).Dart) :
    C.gluedFaceProjection hEuler s ((C.gluedGraph hEuler s).rotation x) =
      G.rotation (C.gluedFaceProjection hEuler s x) ∨
    C.gluedFaceProjection hEuler s ((C.gluedGraph hEuler s).rotation x) =
      G.pairing.twin (C.gluedFaceProjection hEuler s x) := by
  by_cases hx : C.GluedRetained hEuler s x
  · exact Or.inl (C.gluedFaceProjection_rotation_retained hEuler s x hx)
  · rw [C.gluedRetained_iff] at hx
    cases x with
    | top i => exact i.elim0
    | bottom i => exact i.elim0
    | hub h i => exact (hx trivial).elim
    | joint j b =>
      rcases j with (j | j) | i
      · exact (hx trivial).elim
      · exact (hx trivial).elim
      · right
        cases b
        · exact (G.pairing.involutive (C.boundaryEnumeration (!s) i).val).symm
        · rfl

theorem gluedFaceProjection_step (s : Bool) (x : (C.gluedGraph hEuler s).Dart) :
    C.gluedFaceProjection hEuler s ((C.gluedGraph hEuler s).circuitStep x) =
      G.circuitStep (C.gluedFaceProjection hEuler s x) ∨
    C.gluedFaceProjection hEuler s ((C.gluedGraph hEuler s).circuitStep x) =
      C.gluedFaceProjection hEuler s x := by
  rcases C.gluedFaceProjection_rotation hEuler s ((C.gluedGraph hEuler s).pairing.twin x) with he | he
  · rw [C.gluedFaceProjection_pairing] at he
    exact Or.inl he
  · rw [C.gluedFaceProjection_pairing, G.pairing.involutive] at he
    exact Or.inr he

theorem gluedFaceProjection_sameCycle (s : Bool) {x y : (C.gluedGraph hEuler s).Dart}
    (hxy : (C.gluedGraph hEuler s).circuitStep.SameCycle x y) :
    G.circuitStep.SameCycle (C.gluedFaceProjection hEuler s x) (C.gluedFaceProjection hEuler s y) := by
  apply predicate_of_sameCycle (C.gluedGraph hEuler s).circuitStep
    (fun z => G.circuitStep.SameCycle (C.gluedFaceProjection hEuler s x) (C.gluedFaceProjection hEuler s z))
    _ hxy Equiv.Perm.SameCycle.rfl
  intro z hz
  rcases C.gluedFaceProjection_step hEuler s z with he | he
  · rw [he]; exact hz.apply_right
  · rwa [he]

theorem gluingFaceVal_label (s : Bool) (x : C.GluingRaw s) :
    Port.label G.jointLabel (C.gluingFaceVal s x) = Port.label G.jointLabel (C.gluingRawVal s x) := by
  rcases x with (x | ⟨x, b⟩) | x
  · rfl
  · cases b
    · rfl
    · exact G.pairing.label_twin x.val
  · rfl

theorem gluedFaceProjection_label (s : Bool) (x : (C.gluedGraph hEuler s).Dart) :
    Port.label G.jointLabel (C.gluedFaceProjection hEuler s x) =
      Port.label (C.gluedGraph hEuler s).jointLabel x :=
  (C.gluingFaceVal_label s (C.gluedPorts hEuler s x)).trans (C.gluedProjection_label hEuler s x)

theorem gluingFaceVal_germOriginal (s : Bool) (x : {x : G.Dart // C.GermVertex s x.vertex}) :
    C.gluingFaceVal s (.inl (C.germOriginal hEuler s x)) = x.val := by
  rcases (C.germ_vertex_port_iff hEuler s x.val).mp x.property with hu | hf
  · rw [C.germOriginal_of_uncut hEuler s x hu]; rfl
  · rw [C.germOriginal_of_outward hEuler s x hf]; rfl

theorem gluedFaceProjection_germ (s : Bool) (x : (C.germGraph hEuler s).Dart) :
    C.gluedFaceProjection hEuler s
      (compPorts (C.germGraph hEuler s) (C.regionGraph hEuler (!s)) (.inl x)) =
      C.germFaceSource hEuler s ((C.germGraph hEuler s).swapBoundaryPorts x) := by
  unfold gluedFaceProjection
  rw [C.gluedPorts_comp]
  cases x with
  | top i => exact i.elim0
  | bottom i => rfl
  | hub h i => exact C.gluingFaceVal_germOriginal hEuler s ⟨.hub h.val i, h.property⟩
  | joint j b => exact C.gluingFaceVal_germOriginal hEuler s ⟨.joint j.val b, j.property⟩

@[reducible] noncomputable def orientedGluedGraph (s : Bool) : PortGraph P [] [] :=
  (C.regionGraph hEuler (!s)).swapBoundary.comp (C.germGraph hEuler s).swapBoundary

noncomputable def orientedGluedPorts (s : Bool) :
    (C.gluedGraph hEuler s).Dart ≃ (C.orientedGluedGraph hEuler s).Dart :=
  reverseCompPorts (C.germGraph hEuler s) (C.regionGraph hEuler (!s))

noncomputable def orientedFaceProjection (s : Bool) (x : (C.orientedGluedGraph hEuler s).Dart) : G.Dart :=
  C.gluedFaceProjection hEuler s ((C.orientedGluedPorts hEuler s).symm x)

theorem orientedFaceProjection_label (s : Bool) (x : (C.orientedGluedGraph hEuler s).Dart) :
    Port.label G.jointLabel (C.orientedFaceProjection hEuler s x) =
      Port.label (C.orientedGluedGraph hEuler s).jointLabel x := by
  have he := reverseCompPorts_label (C.germGraph hEuler s) (C.regionGraph hEuler (!s))
    ((C.orientedGluedPorts hEuler s).symm x)
  change Port.label (C.orientedGluedGraph hEuler s).jointLabel
    (C.orientedGluedPorts hEuler s ((C.orientedGluedPorts hEuler s).symm x)) = _ at he
  rw [Equiv.apply_symm_apply] at he
  exact (C.gluedFaceProjection_label hEuler s ((C.orientedGluedPorts hEuler s).symm x)).trans he.symm

theorem orientedFaceProjection_germ (s : Bool) (x : (C.germGraph hEuler s).swapBoundary.Dart) :
    C.orientedFaceProjection hEuler s
      (compRightEmbedding (C.regionGraph hEuler (!s)).swapBoundary (C.germGraph hEuler s).swapBoundary x) =
        C.germFaceSource hEuler s x := by
  obtain ⟨x, rfl⟩ := (C.germGraph hEuler s).swapBoundaryPorts.surjective x
  unfold orientedFaceProjection
  have he := reverseCompPorts_left (C.germGraph hEuler s) (C.regionGraph hEuler (!s)) x
  change C.orientedGluedPorts hEuler s
    (compPorts (C.germGraph hEuler s) (C.regionGraph hEuler (!s)) (.inl x)) = _ at he
  change C.gluedFaceProjection hEuler s ((C.orientedGluedPorts hEuler s).symm
    (compPorts (C.regionGraph hEuler (!s)).swapBoundary (C.germGraph hEuler s).swapBoundary
      (.inr ((C.germGraph hEuler s).swapBoundaryPorts x)))) = _
  rw [← he]
  exact (congrArg (C.gluedFaceProjection hEuler s)
    ((C.orientedGluedPorts hEuler s).symm_apply_apply
      (compPorts (C.germGraph hEuler s) (C.regionGraph hEuler (!s)) (.inl x)))).trans
        (C.gluedFaceProjection_germ hEuler s x)

end ThomGame.Pictures.PortGraph.SimpleCircuit
