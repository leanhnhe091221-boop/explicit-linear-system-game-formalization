module

public import ThomGame.Construction.WheelSunBandExclusion
public import ThomGame.Construction.WheelLiftedFaces
public import ThomGame.Pictures.SunCircuitRimLabels

/-!
# No circuit of another constellation index lies wholly in an included sun

Pull a putative circuit back to the actual normalized sun. Distinct
numbered wheel cycles share at most one edge label, so its rim labels
are all equal. The local three-label exclusion contradicts minimality.
This handles the wholly internal case needed in Lemma 11.8.
-/

@[expose] public section
namespace ThomGame.Construction.IncludedWheelSun

open Pictures

variable {i : WheelCycleIndex}
  {w : List (Fin (wheelCycles i).length ⊕ Fin (wheelCycles i).length)}
  {G : PortGraph (sunPresentation (wheelCycles i).length (fun _ => 0)) [] w}
  {v : List (Fin 1889684)} (L : IncludedWheelSun i G v)

theorem no_other_wheel_circuit
    {hw : ∀ z ∈ w, ∃ j, z = Sum.inl j} (hG : G.SunFaceState (wheelCycles i).length_ge_three hw)
    (j : WheelCycleIndex) (hij : i ≠ j) (C : L.graph.SimpleCircuit) :
    ¬ ∀ k : Fin C.length, Port.label L.graph.jointLabel (C.dart k) ∈ Set.range (numberedWheelCycles j).edge := by
  intro hlabels
  let : IsEmpty G.Joint := hG.noJoints
  let D := L.pullbackCircuit C
  have hrim (s : Fin (wheelCycles i).length) :
      (numberedWheelSunEmbedding i).edge (Sum.inr s) ∈ Set.range (numberedWheelCycles i).edge :=
    (numberedWheelSunEmbedding_rim i (Sum.inr s)).mpr ⟨s, rfl⟩
  have hother (k : Fin D.length) (s : Fin (wheelCycles i).length)
      (hs : Port.label G.jointLabel (D.dart k) = Sum.inr s) :
      (numberedWheelSunEmbedding i).edge (Sum.inr s) ∈ Set.range (numberedWheelCycles j).edge := by
    have he : Port.label L.graph.jointLabel (C.dart k) = (numberedWheelSunEmbedding i).edge (Sum.inr s) :=
      (L.pullbackCircuit_label C k).symm.trans (congrArg (numberedWheelSunEmbedding i).edge hs)
    exact he ▸ hlabels k
  by_cases hex : ∃ (k : Fin D.length) (s : Fin (wheelCycles i).length),
      Port.label G.jointLabel (D.dart k) = Sum.inr s
  · obtain ⟨k₀, s₀, hs₀⟩ := hex
    apply hG.no_sunBand_circuit.no_single_rim_label D s₀
    intro k s hs
    apply Sum.inr.inj
    apply (numberedWheelSunEmbedding i).edge.injective
    exact numberedWheelCycles_intersection_unique i j hij _ _
      (hrim s) (hother k s hs) (hrim s₀) (hother k₀ s₀ hs₀)
  · have hn := (wheelCycles i).length_ge_three
    apply hG.no_sunBand_circuit.no_single_rim_label D ⟨0, by omega⟩
    intro k s hs
    exact (hex ⟨k, s, hs⟩).elim

theorem circuit_has_label_outside_other_wheel
    {hw : ∀ z ∈ w, ∃ j, z = Sum.inl j} (hG : G.SunFaceState (wheelCycles i).length_ge_three hw)
    (j : WheelCycleIndex) (hij : i ≠ j) (C : L.graph.SimpleCircuit) :
    ∃ k : Fin C.length, Port.label L.graph.jointLabel (C.dart k) ∉ Set.range (numberedWheelCycles j).edge := by
  classical
  exact not_forall.mp (L.no_other_wheel_circuit hG j hij C)

end ThomGame.Construction.IncludedWheelSun
