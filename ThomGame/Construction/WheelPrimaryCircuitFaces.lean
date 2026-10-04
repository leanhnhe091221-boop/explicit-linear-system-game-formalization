module

public import ThomGame.Construction.WheelGluedCircuitClassification
public import ThomGame.Pictures.RimCircuitUniqueness

/-!
# Every primary target circuit is facial or inherited from the complement

A primary rim port from the normalized sun belongs to a specified
facial rim that survives the actual gluing and smoothing. The unique
restricted rim component identifies any target circuit through that
port with this facial witness. The general gluing classification then
leaves only exact complementary-region preimages for non-facial cycles.
-/

@[expose] public section
namespace ThomGame.Construction.IncludedWheelSun

open Pictures PortGraph RibbonConnectivity

variable {i : WheelCycleIndex}
  {w : List (Fin (wheelCycles i).length ⊕ Fin (wheelCycles i).length)}
  {K : PortGraph (sunPresentation (wheelCycles i).length (fun _ => 0)) [] w}
  {v : List (Fin 1889684)} (L : IncludedWheelSun i K v.reverse) (E : SigmaGraph v [])

theorem orientedRimCircuit_rim (a : L.graph.RimDart (numberedWheelCycles i))
    (k : Fin (L.orientedRimCircuit E a).length) :
    Port.label (L.orientedGlue E).graph.jointLabel ((L.orientedRimCircuit E a).dart k) ∈
      Set.range (numberedWheelCycles i).edge := by
  change Port.label (L.orientedGlue E).graph.jointLabel ((L.orientedRimCircuit E a).port (k, false)) ∈ _
  rw [← (L.orientedGlue E).trace.portLabel, L.orientedRimCircuit_port,
    compRightEmbedding_label, L.topPorts_label]
  exact L.graph.rimSimpleCircuit_rim (numberedWheelCycles i) (by simp) L.noRim a k

theorem orientedRimCircuit_first (a : L.graph.RimDart (numberedWheelCycles i)) :
    (L.orientedGlue E).trace.portEmbedding ((L.orientedRimCircuit E a).dart 0) =
      compRightEmbedding E.swapBoundary L.topGraph (L.topPorts a.val) :=
  L.orientedRimCircuit_port E a (0, false)

theorem oriented_primary_face_of_right_dart
    (hEuler : eulerDefect (L.orientedGlue E).graph.pairing.perm (L.orientedGlue E).graph.circuitStep = 0)
    (C : (L.orientedGlue E).graph.SimpleCircuit)
    (hlabels : ∀ k : Fin C.length,
      Port.label (L.orientedGlue E).graph.jointLabel (C.dart k) ∈ Set.range (numberedWheelCycles i).edge)
    (k : Fin C.length) (a : L.graph.RimDart (numberedWheelCycles i))
    (he : (L.orientedGlue E).trace.portEmbedding (C.dart k) =
      compRightEmbedding E.swapBoundary L.topGraph (L.topPorts a.val)) :
    ∃ side, C.BoundsFaceOrbit side := by
  let F := L.orientedRimCircuit E a
  have hshared : C.dart k = F.dart 0 := (L.orientedGlue E).trace.portEmbedding.injective
    (he.trans (L.orientedRimCircuit_first E a).symm)
  obtain ⟨⟨side, hface⟩, _⟩ := L.orientedRimCircuit_facial_cover E a
  apply C.exists_face_of_common_rim_port (numberedWheelCycles i) (by simp) (by simp)
    hlabels F (L.orientedRimCircuit_rim E a)
    ((L.orientedGlue E).graph.dualEuler_eq_twice_components hEuler) (C.dart k)
    ⟨(k, false), rfl⟩ ?_ side hface
  exact ⟨(0, false), hshared.symm⟩

variable [IsEmpty E.Joint]

theorem oriented_primary_facial_or_exterior
    (hEuler : eulerDefect (L.orientedGlue E).graph.pairing.perm (L.orientedGlue E).graph.circuitStep = 0)
    (C : (L.orientedGlue E).graph.SimpleCircuit)
    (hlabels : ∀ k : Fin C.length,
      Port.label (L.orientedGlue E).graph.jointLabel (C.dart k) ∈ Set.range (numberedWheelCycles i).edge) :
    (∃ side, C.BoundsFaceOrbit side) ∨ (L.orientedGlue E).HasLeftPreimage C := by
  rcases L.oriented_primary_circuit_input_preimage E C hlabels with hleft | ⟨D, hlen, hp⟩
  · exact Or.inr hleft
  · let x := D.dart 0
    let k : Fin C.length := finCongr hlen 0
    have he : (L.orientedGlue E).trace.portEmbedding (C.dart k) =
        compRightEmbedding E.swapBoundary L.topGraph x := (hp (0, false)).symm
    have hl : Port.label L.graph.jointLabel (L.topPorts.symm x) =
        Port.label (L.orientedGlue E).graph.jointLabel (C.dart k) := by
      rw [← L.topPorts_label, Equiv.apply_symm_apply]
      exact (compRightEmbedding_label E.swapBoundary L.topGraph x).symm.trans
        ((congrArg (Port.label (E.swapBoundary.comp L.topGraph).jointLabel) he.symm).trans
          ((L.orientedGlue E).trace.portLabel _))
    let a : L.graph.RimDart (numberedWheelCycles i) := ⟨L.topPorts.symm x, hl ▸ hlabels k⟩
    apply Or.inl
    apply L.oriented_primary_face_of_right_dart E hEuler C hlabels k a
    change _ = compRightEmbedding E.swapBoundary L.topGraph (L.topPorts (L.topPorts.symm x))
    rw [Equiv.apply_symm_apply]
    exact he

theorem oriented_primary_nonfacial_exterior
    (hEuler : eulerDefect (L.orientedGlue E).graph.pairing.perm (L.orientedGlue E).graph.circuitStep = 0)
    (C : (L.orientedGlue E).graph.SimpleCircuit)
    (hlabels : ∀ k : Fin C.length,
      Port.label (L.orientedGlue E).graph.jointLabel (C.dart k) ∈ Set.range (numberedWheelCycles i).edge)
    (hnot : ¬ ∃ side, C.BoundsFaceOrbit side) : (L.orientedGlue E).HasLeftPreimage C :=
  (L.oriented_primary_facial_or_exterior E hEuler C hlabels).resolve_left hnot

end ThomGame.Construction.IncludedWheelSun

namespace ThomGame.Construction

open Pictures

variable {d : SigmaDiagram [] []} {H : SigmaGraph [] []} 
  (t : SigmaGraphWitness d H) [IsEmpty H.Joint]
  (i : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i)) (side : Bool)
  {w : List (Fin (wheelCycles i).length ⊕ Fin (wheelCycles i).length)}
  {K : PortGraph (sunPresentation (wheelCycles i).length (fun _ => 0)) [] w}
  (L : IncludedWheelSun i K ((closedSigmaRimCircuit H i a).frontierWord (!side)).reverse)

theorem includedSunOrientedGluing_primary_facial_or_exterior
    (C : (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!side))).graph.SimpleCircuit)
    (hlabels : ∀ k : Fin C.length,
      Port.label (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!side))).graph.jointLabel (C.dart k) ∈
        Set.range (numberedWheelCycles i).edge) :
    (∃ s, C.BoundsFaceOrbit s) ∨
      (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!side))).HasLeftPreimage C := by
  let : IsEmpty (smoothedSigmaRimRegionGraph t i a (!side)).Joint := ⟨fun j => isEmptyElim j.val⟩
  exact L.oriented_primary_facial_or_exterior _ (includedSunOrientedGluing_euler t i a side L) C hlabels

end ThomGame.Construction
