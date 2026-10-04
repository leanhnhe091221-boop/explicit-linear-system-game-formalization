module

public import ThomGame.Construction.WheelMinimalRecovery
public import ThomGame.Pictures.LiftedGermSupport

/-! # Lifting the original numbered constellation faces into the actual oriented composition -/

@[expose] public section
namespace ThomGame.Construction

open Pictures

theorem numberedWheelCycles_edge_range (i : WheelCycleIndex) (e : Fin 1889684) :
    e ∈ Set.range (numberedWheelCycles i).edge ↔ colEquiv.symm e ∈ Set.range (wheelCycles i).edge := by
  have h {n : Nat} (f : Fin n → Col) :
      (∃ k, colEquiv (f k) = e) ↔ ∃ k, f k = colEquiv.symm e := by
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, (colEquiv.symm_apply_apply (f k)).symm.trans (congrArg colEquiv.symm hk)⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, (congrArg colEquiv hk).trans (colEquiv.apply_symm_apply e)⟩
  rcases i with r | ⟨r, j⟩
  · exact h (wheelCycles (.inl r)).edge
  · exact h (wheelCycles (.inr ⟨r, j⟩)).edge

theorem numberedWheelCycles_intersection_unique (i j : WheelCycleIndex) (hij : i ≠ j)
    (e f : Fin 1889684)
    (hei : e ∈ Set.range (numberedWheelCycles i).edge) (hej : e ∈ Set.range (numberedWheelCycles j).edge)
    (hfi : f ∈ Set.range (numberedWheelCycles i).edge) (hfj : f ∈ Set.range (numberedWheelCycles j).edge) : e = f :=
  colEquiv.symm.injective (wheelCycles_intersection_unique i j hij _ _
    ((numberedWheelCycles_edge_range i e).mp hei) ((numberedWheelCycles_edge_range j e).mp hej)
    ((numberedWheelCycles_edge_range i f).mp hfi) ((numberedWheelCycles_edge_range j f).mp hfj))

variable {d : SigmaDiagram [] []} {H : SigmaGraph [] []} 
  (t : SigmaGraphWitness d H) [IsEmpty H.Joint] (hmin : d.Minimal) (hs : d.sign = 1)
  (i j : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i))
  (b : H.RimDart (numberedWheelCycles j)) (s faceSide : Bool)
  (hf : (closedSigmaRimCircuit H j b).BoundsFaceOrbit faceSide)

@[reducible] noncomputable def liftedSigmaRimCircuit :
    ((smoothedSigmaRimRegionGraph t i a (!s)).swapBoundary.comp
      (smoothedSigmaRimGermGraph t i a s).swapBoundary).SimpleCircuit :=
  (closedSigmaRimCircuit H i a).orientedLiftedCircuit
    (t.dualEuler)
    (reduced_minimal_odd_sigma_reachable t hmin hs) s (closedSigmaRimCircuit H j b) faceSide hf

theorem liftedSigmaRimCircuit_face :
    (liftedSigmaRimCircuit t hmin hs i j a b s faceSide hf).BoundsFaceOrbit false :=
  (closedSigmaRimCircuit H i a).orientedLiftedCircuit_face
    (t.dualEuler)
    (reduced_minimal_odd_sigma_reachable t hmin hs) s (closedSigmaRimCircuit H j b) faceSide hf

variable (entry : H.Dart) (he : (closedSigmaRimCircuit H i a).Frontier (!s) entry)
  (heface : H.circuitStep.SameCycle (H.pairing.twin entry) ((closedSigmaRimCircuit H j b).port (0, faceSide)))

include he heface in
theorem liftedSigmaRimCircuit_supported (hij : i ≠ j) :
    (liftedSigmaRimCircuit t hmin hs i j a b s faceSide hf).SupportedByQuads false :=
  H.orientedLiftedRimCircuit_supported (numberedWheelCycles i) (numberedWheelCycles j) a b
    (numberedWheelCycles_intersection_unique i j hij)
    (t.dualEuler)
    (reduced_minimal_odd_sigma_reachable t hmin hs) s faceSide hf entry he heface

include he heface in
theorem liftedSigmaRimCircuit_crosses :
    ∃ k x, (liftedSigmaRimCircuit t hmin hs i j a b s faceSide hf).port (k, false) =
      PortGraph.compRightEmbedding (smoothedSigmaRimRegionGraph t i a (!s)).swapBoundary
        (smoothedSigmaRimGermGraph t i a s).swapBoundary x :=
  H.orientedLiftedRimCircuit_crosses (numberedWheelCycles i) (numberedWheelCycles j) a b
    (t.dualEuler)
    (reduced_minimal_odd_sigma_reachable t hmin hs) s faceSide hf entry he heface

end ThomGame.Construction
