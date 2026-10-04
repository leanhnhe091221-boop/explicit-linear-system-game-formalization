module

public import ThomGame.Pictures.GluedFaceSimplicity
public import ThomGame.Pictures.ReducedMinimalRecovery
public import ThomGame.Pictures.CircuitTrace
public import ThomGame.Pictures.CircleFreeCircuitRecovery

/-!
# Lifting an original simple face through the germ-region subdivision

The recovered component supplies the original ports. Enumerating the
actual subdivided face orbit adds the necessary seam vertices. The
result is simple, retains every original face port once, and transports
to the composition order used by the actual germ replacement.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open RibbonConnectivity

variable {R S : Type*} {P : InvolutionPresentation R S} {G : PortGraph P [] []}
  (C : G.SimpleCircuit)
  (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
    2 * Nat.card (Component G.circuitStep G.pairing.perm))
  (hc : ∀ x y : G.Vertex, G.Reachable x y) (s : Bool)

noncomputable def gluedLiftPort (x : G.Dart) : (C.gluedGraph hEuler s).Dart :=
  (C.germReduction hEuler s).trace.portEmbedding ((C.recoveredAllPorts hEuler hc s).symm x)

theorem gluedLiftPort_retained (x : G.Dart) :
    C.GluedRetained hEuler s (C.gluedLiftPort hEuler hc s x) :=
  C.germReduction_port_retained hEuler s ((C.recoveredAllPorts hEuler hc s).symm x)

theorem gluedTerminal_retained (x : (C.gluedGraph hEuler s).Dart)
    (hx : (C.gluedGraph hEuler s).Terminal x) : C.GluedRetained hEuler s x := by
  rw [C.gluedRetained_iff]
  cases x with
  | top i => exact i.elim0
  | bottom i => exact i.elim0
  | hub h i => trivial
  | joint j b => exact hx.elim

theorem gluedRetained_terminal [IsEmpty G.Joint] (x : (C.gluedGraph hEuler s).Dart)
    (hx : C.GluedRetained hEuler s x) : (C.gluedGraph hEuler s).Terminal x := by
  rw [C.gluedRetained_iff] at hx
  cases x with
  | top i => exact i.elim0
  | bottom i => exact i.elim0
  | hub h i => trivial
  | joint j b =>
    rcases j with (j | j) | i
    · exact isEmptyElim j.val
    · exact isEmptyElim j.val
    · exact hx.elim

theorem gluedLiftPort_projection (x : G.Dart) :
    C.gluedFaceProjection hEuler s (C.gluedLiftPort hEuler hc s x) = x := by
  rw [C.gluedFaceProjection_retained hEuler s _ (C.gluedLiftPort_retained hEuler hc s x)]
  exact (C.recoveredPorts_val hEuler s ((C.recoveredAllPorts hEuler hc s).symm x)).symm.trans
    ((C.recoveredAllPorts hEuler hc s).apply_symm_apply x)

theorem recoveredAllPorts_step (x : (C.germReduction hEuler s).graph.Dart) :
    C.recoveredAllPorts hEuler hc s ((C.germReduction hEuler s).graph.circuitStep x) =
      G.circuitStep (C.recoveredAllPorts hEuler hc s x) := by
  rw [(C.germReduction hEuler s).graph.circuitStep_apply, C.recoveredAllPorts_rotation,
    C.recoveredAllPorts_twin]
  rfl

theorem gluedLiftPort_sameCycle (x y : G.Dart) :
    (C.gluedGraph hEuler s).circuitStep.SameCycle
      (C.gluedLiftPort hEuler hc s x) (C.gluedLiftPort hEuler hc s y) ↔ G.circuitStep.SameCycle x y := by
  change (C.gluedGraph hEuler s).circuitStep.SameCycle
    ((C.germReduction hEuler s).trace.portEmbedding ((C.recoveredAllPorts hEuler hc s).symm x))
    ((C.germReduction hEuler s).trace.portEmbedding ((C.recoveredAllPorts hEuler hc s).symm y)) ↔ _
  rw [← (C.gluedGraph hEuler s).circuit_eq_iff,
    ← (C.germReduction hEuler s).trace.sameCircuit_iff,
    (C.germReduction hEuler s).graph.circuit_eq_iff]
  have he := FiniteReturn.sameCycle_congr (C.germReduction hEuler s).graph.circuitStep G.circuitStep
    (C.recoveredAllPorts hEuler hc s) (fun z => (C.recoveredAllPorts_step hEuler hc s z).symm)
    ((C.recoveredAllPorts hEuler hc s).symm x) ((C.recoveredAllPorts hEuler hc s).symm y)
  simpa only [Equiv.apply_symm_apply] using he

theorem retained_eq_gluedLift {x : (C.gluedGraph hEuler s).Dart}
    (hx : C.GluedRetained hEuler s x) :
    x = C.gluedLiftPort hEuler hc s (C.gluedFaceProjection hEuler s x) :=
  C.gluedFaceProjection_injective_retained hEuler s hx
    (C.gluedLiftPort_retained hEuler hc s _) (C.gluedLiftPort_projection hEuler hc s _).symm

theorem gluedFace_sameCycle_lift (x : (C.gluedGraph hEuler s).Dart) :
    (C.gluedGraph hEuler s).circuitStep.SameCycle x
      (C.gluedLiftPort hEuler hc s (C.gluedFaceProjection hEuler s x)) := by
  obtain ⟨y, hy⟩ := (C.germReduction hEuler s).trace.every_circuit_meets_image x
  have he := C.retained_eq_gluedLift hEuler hc s (C.germReduction_port_retained hEuler s y)
  have hf := (C.gluedFaceProjection_sameCycle hEuler s hy).symm
  rw [he] at hy
  exact hy.trans ((C.gluedLiftPort_sameCycle hEuler hc s _ _).mpr hf)

include hc in
theorem gluedFaceProjection_sameCycle_iff (x y : (C.gluedGraph hEuler s).Dart) :
    (C.gluedGraph hEuler s).circuitStep.SameCycle x y ↔
      G.circuitStep.SameCycle (C.gluedFaceProjection hEuler s x) (C.gluedFaceProjection hEuler s y) := by
  constructor
  · exact C.gluedFaceProjection_sameCycle hEuler s
  · intro h
    exact (C.gluedFace_sameCycle_lift hEuler hc s x).trans
      (((C.gluedLiftPort_sameCycle hEuler hc s _ _).mpr h).trans
        (C.gluedFace_sameCycle_lift hEuler hc s y).symm)

noncomputable def orientedLiftPort (x : G.Dart) : (C.orientedGluedGraph hEuler s).Dart :=
  C.orientedGluedPorts hEuler s (C.gluedLiftPort hEuler hc s x)

theorem orientedLiftPort_projection (x : G.Dart) :
    C.orientedFaceProjection hEuler s (C.orientedLiftPort hEuler hc s x) = x := by
  unfold orientedLiftPort orientedFaceProjection
  rw [Equiv.symm_apply_apply]
  exact C.gluedLiftPort_projection hEuler hc s x

theorem orientedLiftPort_label (x : G.Dart) :
    Port.label (C.orientedGluedGraph hEuler s).jointLabel (C.orientedLiftPort hEuler hc s x) =
      Port.label G.jointLabel x := by
  rw [← C.orientedFaceProjection_label, C.orientedLiftPort_projection]

theorem orientedLiftPort_terminal [IsEmpty G.Joint] (x : G.Dart) :
    (C.orientedGluedGraph hEuler s).Terminal (C.orientedLiftPort hEuler hc s x) :=
  (reverseCompPorts_terminal (C.germGraph hEuler s) (C.regionGraph hEuler (!s)) _).mpr
    (C.gluedRetained_terminal hEuler s _ (C.gluedLiftPort_retained hEuler hc s x))

variable (D : G.SimpleCircuit) (side : Bool) (hf : D.BoundsFaceOrbit side)

theorem liftedFace_projection {x : (C.gluedGraph hEuler s).Dart}
    (hx : (C.gluedGraph hEuler s).circuitStep.SameCycle x
      (C.gluedLiftPort hEuler hc s (D.port (0, side)))) :
    G.circuitStep.SameCycle (C.gluedFaceProjection hEuler s x) (D.port (0, side)) := by
  have he := C.gluedFaceProjection_sameCycle hEuler s hx
  rwa [C.gluedLiftPort_projection] at he

@[reducible] noncomputable def liftedGermCircuit : (C.gluedGraph hEuler s).SimpleCircuit :=
  (C.gluedGraph hEuler s).facialCircuitOfOrbit (C.gluedLiftPort hEuler hc s (D.port (0, side)))
    (fun _ _ hx hy hv => C.gluedFace_vertex_injective hEuler s D side hf
      (C.liftedFace_projection hEuler hc s D side hx) (C.liftedFace_projection hEuler hc s D side hy) hv)
    (fun x hx => C.gluedFace_rotation_ne_self hEuler s D side hf x
      (C.liftedFace_projection hEuler hc s D side hx))

theorem liftedGermCircuit_face : (C.liftedGermCircuit hEuler hc s D side hf).BoundsFaceOrbit false :=
  (C.gluedGraph hEuler s).facialCircuitOfOrbit_face _ _ _

theorem liftedGermCircuit_source (j : Fin (C.liftedGermCircuit hEuler hc s D side hf).length) :
    G.circuitStep.SameCycle
      (C.gluedFaceProjection hEuler s ((C.liftedGermCircuit hEuler hc s D side hf).dart j))
      (D.port (0, side)) :=
  C.liftedFace_projection hEuler hc s D side (OrbitEnumeration.dart_sameCycle _ _ j).symm

theorem liftedGermCircuit_range (x : (C.gluedGraph hEuler s).Dart) :
    (∃ j, (C.liftedGermCircuit hEuler hc s D side hf).dart j = x) ↔
      G.circuitStep.SameCycle (C.gluedFaceProjection hEuler s x) (D.port (0, side)) := by
  constructor
  · rintro ⟨j, rfl⟩
    exact C.liftedGermCircuit_source hEuler hc s D side hf j
  · intro hx
    have he := (C.gluedFaceProjection_sameCycle_iff hEuler hc s x
      (C.gluedLiftPort hEuler hc s (D.port (0, side)))).mpr
      (by rw [C.gluedLiftPort_projection]; exact hx)
    exact (OrbitEnumeration.dart_range _ _ x).mpr he.symm

theorem liftedGermCircuit_complete (i : Fin D.length) :
    ∃! j : Fin (C.liftedGermCircuit hEuler hc s D side hf).length,
      (C.liftedGermCircuit hEuler hc s D side hf).dart j = C.gluedLiftPort hEuler hc s (D.port (i, side)) := by
  have hx := (C.gluedLiftPort_sameCycle hEuler hc s (D.port (i, side)) (D.port (0, side))).mpr
    ((hf _).mpr ⟨i, rfl⟩)
  obtain ⟨j, hj⟩ := (OrbitEnumeration.dart_range (C.gluedGraph hEuler s).circuitStep
    (C.gluedLiftPort hEuler hc s (D.port (0, side))) _).mpr hx.symm
  exact ⟨j, hj, fun k hk => (C.liftedGermCircuit hEuler hc s D side hf).dart.injective (hk.trans hj.symm)⟩

theorem liftedGermCircuit_retained_original
    (j : Fin (C.liftedGermCircuit hEuler hc s D side hf).length)
    (hj : C.GluedRetained hEuler s ((C.liftedGermCircuit hEuler hc s D side hf).dart j)) :
    ∃ i : Fin D.length, (C.liftedGermCircuit hEuler hc s D side hf).dart j =
      C.gluedLiftPort hEuler hc s (D.port (i, side)) := by
  obtain ⟨i, hi⟩ := (hf _).mp (C.liftedGermCircuit_source hEuler hc s D side hf j)
  refine ⟨i, C.gluedFaceProjection_injective_retained hEuler s hj
    (C.gluedLiftPort_retained hEuler hc s (D.port (i, side))) ?_⟩
  rw [C.gluedLiftPort_projection]
  exact hi.symm

@[reducible] noncomputable def orientedLiftedCircuit : (C.orientedGluedGraph hEuler s).SimpleCircuit :=
  (C.liftedGermCircuit hEuler hc s D side hf).reverseComposition
    (C.germGraph hEuler s) (C.regionGraph hEuler (!s))

theorem orientedLiftedCircuit_face : (C.orientedLiftedCircuit hEuler hc s D side hf).BoundsFaceOrbit false :=
  (C.liftedGermCircuit hEuler hc s D side hf).reverseComposition_face
    (C.germGraph hEuler s) (C.regionGraph hEuler (!s)) false
    (C.liftedGermCircuit_face hEuler hc s D side hf)

theorem orientedLiftedCircuit_dart (j : Fin (C.liftedGermCircuit hEuler hc s D side hf).length) :
    (C.orientedLiftedCircuit hEuler hc s D side hf).dart j =
      C.orientedGluedPorts hEuler s ((C.liftedGermCircuit hEuler hc s D side hf).dart j) := rfl

theorem orientedLiftedCircuit_complete (i : Fin D.length) :
    ∃! j : Fin (C.orientedLiftedCircuit hEuler hc s D side hf).length,
      (C.orientedLiftedCircuit hEuler hc s D side hf).dart j =
        C.orientedLiftPort hEuler hc s (D.port (i, side)) := by
  obtain ⟨j, hj, _⟩ := C.liftedGermCircuit_complete hEuler hc s D side hf i
  have he : (C.orientedLiftedCircuit hEuler hc s D side hf).dart j =
      C.orientedLiftPort hEuler hc s (D.port (i, side)) := congrArg (C.orientedGluedPorts hEuler s) hj
  exact ⟨j, he, fun k hk => (C.orientedLiftedCircuit hEuler hc s D side hf).dart.injective (hk.trans he.symm)⟩

theorem orientedLiftedCircuit_terminal_original
    (j : Fin (C.orientedLiftedCircuit hEuler hc s D side hf).length)
    (hj : (C.orientedGluedGraph hEuler s).Terminal
      ((C.orientedLiftedCircuit hEuler hc s D side hf).dart j)) :
    ∃ i : Fin D.length, (C.orientedLiftedCircuit hEuler hc s D side hf).dart j =
      C.orientedLiftPort hEuler hc s (D.port (i, side)) := by
  have ht := (reverseCompPorts_terminal (C.germGraph hEuler s) (C.regionGraph hEuler (!s))
    ((C.liftedGermCircuit hEuler hc s D side hf).dart j)).mp hj
  obtain ⟨i, hi⟩ := C.liftedGermCircuit_retained_original hEuler hc s D side hf j
    (C.gluedTerminal_retained hEuler s _ ht)
  exact ⟨i, congrArg (C.orientedGluedPorts hEuler s) hi⟩

theorem orientedLiftedCircuit_source
    (j : Fin (C.orientedLiftedCircuit hEuler hc s D side hf).length) :
    G.circuitStep.SameCycle
      (C.orientedFaceProjection hEuler s ((C.orientedLiftedCircuit hEuler hc s D side hf).dart j))
      (D.port (0, side)) := by
  change G.circuitStep.SameCycle
    (C.gluedFaceProjection hEuler s ((C.orientedGluedPorts hEuler s).symm
      (C.orientedGluedPorts hEuler s ((C.liftedGermCircuit hEuler hc s D side hf).dart j)))) _
  rw [Equiv.symm_apply_apply]
  exact C.liftedGermCircuit_source hEuler hc s D side hf j

theorem orientedLiftedCircuit_range (x : (C.orientedGluedGraph hEuler s).Dart) :
    (∃ j, (C.orientedLiftedCircuit hEuler hc s D side hf).dart j = x) ↔
      G.circuitStep.SameCycle (C.orientedFaceProjection hEuler s x) (D.port (0, side)) := by
  constructor
  · rintro ⟨j, rfl⟩
    exact C.orientedLiftedCircuit_source hEuler hc s D side hf j
  · intro hx
    obtain ⟨j, hj⟩ := (C.liftedGermCircuit_range hEuler hc s D side hf
      ((C.orientedGluedPorts hEuler s).symm x)).mpr hx
    refine ⟨j, ?_⟩
    change C.orientedGluedPorts hEuler s ((C.liftedGermCircuit hEuler hc s D side hf).dart j) = x
    rw [hj, Equiv.apply_symm_apply]

end ThomGame.Pictures.PortGraph.SimpleCircuit
