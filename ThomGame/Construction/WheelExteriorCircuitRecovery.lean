module

public import ThomGame.Construction.WheelPrimaryCircuitFaces
public import ThomGame.Pictures.GluedPreimageFaces

/-!
# Exterior target circuits recover in the original numbered graph

The actual complementary-region preimage gives an original circuit
with the same length and labels, whose vertices avoid the replaced
germ. Original faciality transfers to the arbitrary target circuit.
In particular, every new nonfacial primary circuit comes from an old
nonfacial circuit disjoint from the selected original circuit.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures PortGraph

variable {d : SigmaDiagram [] []} {H : SigmaGraph [] []} 
  (t : SigmaGraphWitness d H)

include t in
theorem sigma_labelled_circuit_facial_of_rims (j : WheelCycleIndex)
    (hfaces : ∀ b : H.RimDart (numberedWheelCycles j),
      ∃ s, (closedSigmaRimCircuit H j b).BoundsFaceOrbit s)
    (D : H.SimpleCircuit)
    (hlabels : ∀ k : Fin D.length, Port.label H.jointLabel (D.dart k) ∈
      Set.range (numberedWheelCycles j).edge) : ∃ s, D.BoundsFaceOrbit s := by
  let b : H.RimDart (numberedWheelCycles j) := ⟨D.dart 0, hlabels 0⟩
  obtain ⟨side, hf⟩ := hfaces b
  exact D.exists_face_of_common_rim_port (numberedWheelCycles j) (by simp) (by simp)
    hlabels (closedSigmaRimCircuit H j b)
    (H.rimSimpleCircuit_rim (numberedWheelCycles j) (by simp) (by simp) b)
    (t.dualEuler) (D.dart 0)
    ⟨(0, false), rfl⟩ ⟨(0, false), rfl⟩ side hf

variable (i : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i)) (side : Bool)
  {w : List (Fin (wheelCycles i).length ⊕ Fin (wheelCycles i).length)}
  {K : PortGraph (sunPresentation (wheelCycles i).length (fun _ => 0)) [] w}
  (L : IncludedWheelSun i K ((closedSigmaRimCircuit H i a).frontierWord (!side)).reverse)
  (C : (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!side))).graph.SimpleCircuit)

theorem includedSunOrientedGluing_exterior_original
    (hleft : (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!side))).HasLeftPreimage C) :
    ∃ D : H.SimpleCircuit, ∃ hlen : D.length = C.length,
      (∀ x : Fin D.length × Bool, Port.label H.jointLabel (D.port x) =
        Port.label (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!side))).graph.jointLabel
          (C.port (finCongr hlen x.1, x.2))) ∧
      (∀ x : Fin D.length × Bool, ¬ (closedSigmaRimCircuit H i a).GermVertex side (D.port x).vertex) ∧
      (∀ s, D.BoundsFaceOrbit s → C.BoundsFaceOrbit s) := by
  simpa only [Bool.not_not] using
    (closedSigmaRimCircuit H i a).exists_original_of_exterior_preimage
      (t.dualEuler) (!side)
      (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!side))) C hleft

theorem includedSunOrientedGluing_exterior_facial (j : WheelCycleIndex)
    (hfaces : ∀ b : H.RimDart (numberedWheelCycles j),
      ∃ s, (closedSigmaRimCircuit H j b).BoundsFaceOrbit s)
    (hlabels : ∀ k : Fin C.length,
      Port.label (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!side))).graph.jointLabel
        (C.dart k) ∈ Set.range (numberedWheelCycles j).edge)
    (hleft : (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!side))).HasLeftPreimage C) :
    ∃ s, C.BoundsFaceOrbit s := by
  obtain ⟨D, hlen, hl, _, hf⟩ := includedSunOrientedGluing_exterior_original t i a side L C hleft
  have hD (k : Fin D.length) : Port.label H.jointLabel (D.dart k) ∈
      Set.range (numberedWheelCycles j).edge := by
    change Port.label H.jointLabel (D.port (k, false)) ∈ _
    rw [hl]
    exact hlabels _
  obtain ⟨s, hs⟩ := sigma_labelled_circuit_facial_of_rims t j hfaces D hD
  exact ⟨s, hf s hs⟩

variable [IsEmpty H.Joint]

theorem includedSunOrientedGluing_primary_nonfacial_original
    (hlabels : ∀ k : Fin C.length,
      Port.label (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!side))).graph.jointLabel
        (C.dart k) ∈ Set.range (numberedWheelCycles i).edge)
    (hn : ¬ ∃ s, C.BoundsFaceOrbit s) :
    ∃ D : H.SimpleCircuit, D.length = C.length ∧
      (∀ k : Fin D.length, Port.label H.jointLabel (D.dart k) ∈ Set.range (numberedWheelCycles i).edge) ∧
      (∀ x : Fin D.length × Bool, ¬ (closedSigmaRimCircuit H i a).GermVertex side (D.port x).vertex) ∧
      (¬ ∃ s, D.BoundsFaceOrbit s) ∧
      (∀ x : H.Dart, D.Marked x → ¬ (closedSigmaRimCircuit H i a).Marked x) := by
  have hleft := (includedSunOrientedGluing_primary_facial_or_exterior t i a side L C hlabels).resolve_left hn
  obtain ⟨D, hlen, hl, hout, hf⟩ := includedSunOrientedGluing_exterior_original t i a side L C hleft
  refine ⟨D, hlen, ?_, hout, ?_, ?_⟩
  · intro k
    change Port.label H.jointLabel (D.port (k, false)) ∈ _
    rw [hl]
    exact hlabels _
  · rintro ⟨s, hs⟩
    exact hn ⟨s, hf s hs⟩
  · intro x hx hb
    obtain ⟨y, rfl⟩ := hx
    exact hout y (Or.inl ((closedSigmaRimCircuit H i a).marked_onCircuitVertex hb))

theorem includedSunOrientedGluing_other_nonfacial_meets_seam
    {hw : ∀ z ∈ w, ∃ j, z = Sum.inl j} (hK : K.SunFaceState (wheelCycles i).length_ge_three hw)
    (j : WheelCycleIndex) (hij : i ≠ j)
    (hfaces : ∀ b : H.RimDart (numberedWheelCycles j),
      ∃ s, (closedSigmaRimCircuit H j b).BoundsFaceOrbit s)
    (hlabels : ∀ k : Fin C.length,
      Port.label (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!side))).graph.jointLabel
        (C.dart k) ∈ Set.range (numberedWheelCycles j).edge)
    (hn : ¬ ∃ s, C.BoundsFaceOrbit s) :
    (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!side))).MeetsSeam C := by
  let : IsEmpty (smoothedSigmaRimRegionGraph t i a (!side)).Joint := ⟨fun x => isEmptyElim x.val⟩
  exact (L.oriented_other_circuit_seam_or_exterior _ hK j hij C hlabels).resolve_right
    (fun hleft => hn (includedSunOrientedGluing_exterior_facial t i a side L C j hfaces hlabels hleft))

end ThomGame.Construction
