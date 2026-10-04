module

public import ThomGame.Construction.WheelSunFrontier
public import ThomGame.Pictures.SunBandExclusion
public import ThomGame.Pictures.CircuitLocalEmbedding

/-!
# Three-label circuit exclusion in the actual included numbered sun

Every simple circuit in the included graph pulls back along its actual
port equivalence. Injectivity of the numbered edge inclusion then
transfers Lemma 10.6 to the three corresponding matrix-column labels.
-/

@[expose] public section
namespace ThomGame.Construction.IncludedWheelSun

open Pictures

variable {i : WheelCycleIndex}
  {w : List (Fin (wheelCycles i).length ⊕ Fin (wheelCycles i).length)}
  {G : PortGraph (sunPresentation (wheelCycles i).length (fun _ => 0)) [] w}
  {v : List (Fin 1889684)} (L : IncludedWheelSun i G v)

theorem inversePorts_rotation (x : L.graph.Dart) :
    G.rotation (L.ports.symm x) = L.ports.symm (L.graph.rotation x) := by
  apply L.ports.injective
  rw [← L.rotation, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem inversePorts_twin (x : L.graph.Dart) :
    G.pairing.twin (L.ports.symm x) = L.ports.symm (L.graph.pairing.twin x) := by
  apply L.ports.injective
  rw [← L.twin, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

@[reducible] noncomputable def pullbackCircuit (C : L.graph.SimpleCircuit) : G.SimpleCircuit :=
  C.map L.ports.symm.toEmbedding
    (PortGraph.vertex_iff_of_rotation_equiv L.ports.symm L.inversePorts_rotation) L.inversePorts_twin

theorem pullbackCircuit_label (C : L.graph.SimpleCircuit) (k : Fin C.length) :
    (numberedWheelSunEmbedding i).edge (Port.label G.jointLabel ((L.pullbackCircuit C).dart k)) =
      Port.label L.graph.jointLabel (C.dart k) := by
  change (numberedWheelSunEmbedding i).edge (Port.label G.jointLabel (L.ports.symm (C.dart k))) = _
  rw [← L.label, Equiv.apply_symm_apply]

def NumberedBandLabel (j : Fin (wheelCycles i).length) (x : Fin 1889684) : Prop :=
  ∃ z, PortGraph.SunBandLabel j z ∧ (numberedWheelSunEmbedding i).edge z = x

theorem no_numberedBand_circuit (hG : G.NoSunBandCircuit) (C : L.graph.SimpleCircuit)
    (j : Fin (wheelCycles i).length) :
    ¬ ∀ k : Fin C.length, NumberedBandLabel (i := i) j (Port.label L.graph.jointLabel (C.dart k)) := by
  intro hband
  apply hG (L.pullbackCircuit C) j
  intro k
  obtain ⟨z, hz, he⟩ := hband k
  have he' := (numberedWheelSunEmbedding i).edge.injective ((L.pullbackCircuit_label C k).trans he.symm)
  exact he' ▸ hz

theorem no_numberedBand_circuit_of_faceState
    {hw : ∀ z ∈ w, ∃ j, z = Sum.inl j} (hG : G.SunFaceState (wheelCycles i).length_ge_three hw)
    (C : L.graph.SimpleCircuit) (j : Fin (wheelCycles i).length) :
    ¬ ∀ k : Fin C.length, NumberedBandLabel (i := i) j (Port.label L.graph.jointLabel (C.dart k)) :=
  L.no_numberedBand_circuit hG.no_sunBand_circuit C j

end ThomGame.Construction.IncludedWheelSun
