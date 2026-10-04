module

public import ThomGame.Construction.WheelSunInteriorCycles
public import ThomGame.Construction.WheelSunOrientedGluing
public import ThomGame.Pictures.ReducedGluingClassification

/-!
# Classifying target cycles in the actual normalized and smoothed gluing

For another constellation index, every target circuit either meets an
actual interface occurrence or comes entirely from the complementary
region. The normalized sun case is excluded by Lemma 10.6. For the
normalization index itself, boundary labels exclude interface crossings,
so every target circuit has an exact preimage in one of the two inputs.
-/

@[expose] public section
namespace ThomGame.Construction.IncludedWheelSun

open Pictures PortGraph

variable {i : WheelCycleIndex}
  {w : List (Fin (wheelCycles i).length ⊕ Fin (wheelCycles i).length)}
  {K : PortGraph (sunPresentation (wheelCycles i).length (fun _ => 0)) [] w}
  {v : List (Fin 1889684)} (L : IncludedWheelSun i K v.reverse)

@[reducible] noncomputable def fromTopCircuit (C : L.topGraph.SimpleCircuit) : L.graph.SimpleCircuit :=
  C.pullback L.topPorts.toEmbedding (vertex_iff_of_rotation_equiv L.topPorts L.topPorts_rotation)
    L.topPorts_pairing (fun k => L.topPorts.surjective (C.dart k))

theorem fromTopCircuit_port (C : L.topGraph.SimpleCircuit) (x : Fin C.length × Bool) :
    L.topPorts ((L.fromTopCircuit C).port x) = C.port x :=
  C.pullback_port L.topPorts.toEmbedding (vertex_iff_of_rotation_equiv L.topPorts L.topPorts_rotation)
    L.topPorts_pairing (fun k => L.topPorts.surjective (C.dart k)) x

theorem no_other_top_circuit
    {hw : ∀ z ∈ w, ∃ j, z = Sum.inl j} (hK : K.SunFaceState (wheelCycles i).length_ge_three hw)
    (j : WheelCycleIndex) (hij : i ≠ j) (C : L.topGraph.SimpleCircuit) :
    ¬ ∀ k : Fin C.length, Port.label L.topGraph.jointLabel (C.dart k) ∈ Set.range (numberedWheelCycles j).edge := by
  intro hlabels
  apply L.no_other_wheel_circuit hK j hij (L.fromTopCircuit C)
  intro k
  have he := L.fromTopCircuit_port C (k, false)
  have hl : Port.label L.graph.jointLabel ((L.fromTopCircuit C).dart k) =
      Port.label L.topGraph.jointLabel (C.dart k) :=
    (L.topPorts_label _).symm.trans (congrArg (Port.label L.topGraph.jointLabel) he)
  rw [hl]
  exact hlabels k

variable (E : SigmaGraph v []) [IsEmpty E.Joint]

theorem oriented_other_circuit_seam_or_exterior
    {hw : ∀ z ∈ w, ∃ j, z = Sum.inl j} (hK : K.SunFaceState (wheelCycles i).length_ge_three hw)
    (j : WheelCycleIndex) (hij : i ≠ j) (C : (L.orientedGlue E).graph.SimpleCircuit)
    (hlabels : ∀ k : Fin C.length,
      Port.label (L.orientedGlue E).graph.jointLabel (C.dart k) ∈ Set.range (numberedWheelCycles j).edge) :
    (L.orientedGlue E).MeetsSeam C ∨ (L.orientedGlue E).HasLeftPreimage C := by
  let : IsEmpty L.topGraph.Joint := L.topGraph_noJoints
  let : IsEmpty E.swapBoundary.Joint := inferInstanceAs (IsEmpty E.Joint)
  rcases (L.orientedGlue E).classify_circuit C with hseam | hleft | ⟨D, hlen, hp⟩
  · exact Or.inl hseam
  · exact Or.inr hleft
  · apply False.elim
    apply L.no_other_top_circuit hK j hij D
    intro k
    have he := hp (k, false)
    have hl : Port.label L.topGraph.jointLabel (D.dart k) =
        Port.label (L.orientedGlue E).graph.jointLabel (C.dart (finCongr hlen k)) :=
      (compRightEmbedding_label E.swapBoundary L.topGraph _).symm.trans
        ((congrArg (Port.label (E.swapBoundary.comp L.topGraph).jointLabel) he).trans
          ((L.orientedGlue E).trace.portLabel _))
    rw [hl]
    exact hlabels _

theorem oriented_primary_circuit_input_preimage (C : (L.orientedGlue E).graph.SimpleCircuit)
    (hlabels : ∀ k : Fin C.length,
      Port.label (L.orientedGlue E).graph.jointLabel (C.dart k) ∈ Set.range (numberedWheelCycles i).edge) :
    (L.orientedGlue E).HasLeftPreimage C ∨ (L.orientedGlue E).HasRightPreimage C := by
  let : IsEmpty L.topGraph.Joint := L.topGraph_noJoints
  let : IsEmpty E.swapBoundary.Joint := inferInstanceAs (IsEmpty E.Joint)
  rcases (L.orientedGlue E).classify_circuit C with ⟨k, j, _, _, hl⟩ | hinputs
  · have hno : v[j] ∉ Set.range (numberedWheelCycles i).edge :=
      L.noRim _ (List.mem_reverse.mpr (List.get_mem v j))
    exact (hno (hl ▸ hlabels k)).elim
  · exact hinputs

end ThomGame.Construction.IncludedWheelSun
