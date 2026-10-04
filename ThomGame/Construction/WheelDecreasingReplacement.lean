module

public import ThomGame.Construction.WheelOtherCircuitFaces
public import ThomGame.Construction.WheelNonfacialDescent
public import ThomGame.Construction.WheelGermFaceNormalization

/-!
# A concrete decreasing replacement in the actual Sigma graph

Choose a nonfacial stellar rim in an actual closed graph with an
Euler/size/sign witness from a minimal odd diagram. A smoothing supplies
such a witness, but no smoothing or graph isomorphism is required.
The constructed replacement strictly decreases its nonfacial component
count and preserves faciality for all other indices. The actual output
has the same size and sign, is saturated, and has a minimal diagram
witness with exactly its relation multiset. Iteration must keep the
actual graph; no isomorphism to that witness's extracted graph is claimed.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures RibbonConnectivity
open scoped BigOperators

variable {d : SigmaDiagram [] []} {H : SigmaGraph [] []} 
  (t : SigmaGraphWitness d H) [IsEmpty H.Joint]
  (hmin : d.Minimal) (hs : d.sign = 1)
  (i : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i))

include t hmin hs in
theorem smoothedSigmaRim_exists_decreasing_replacement (hi : i ≠ oddWheelCycle)
    (hn : ¬ ∃ side, (closedSigmaRimCircuit H i a).BoundsFaceOrbit side) :
    ∃ H' : SigmaGraph [] [], IsEmpty H'.Joint ∧
      Fintype.card H'.Hub = d.size ∧ H'.sign = 1 ∧
      eulerDefect H'.pairing.perm H'.circuitStep = 0 ∧
      sigmaNonfacialRimCount H' i < sigmaNonfacialRimCount H i ∧
      (∀ j : WheelCycleIndex, i ≠ j → SigmaRimsFacial H j → SigmaRimsFacial H' j) ∧
      ∃ f : SigmaDiagram [] [],
        (f.labels : Multiset (Fin 1417152)) = ∑ h : H'.Hub, ([H'.hubLabel h] : Multiset (Fin 1417152)) ∧
        f.size = d.size ∧ f.sign = 1 ∧ f.Minimal := by
  obtain ⟨side, m, hw, K, q, L, hp, _, hK, _, _, _, hsize, hsign, heuler, hd⟩ :=
    smoothedSigmaRim_exists_face_preserving_normalization t hmin hs i a hi
  refine ⟨(L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!side))).graph,
    inferInstance, hsize, hsign, heuler,
    includedSunOrientedGluing_nonfacial_count_lt t i a side L hn, ?_, hd⟩
  intro j hij hfaces b
  exact germSun_other_rims_facial t hmin hs i a side m hw q L hp hK j hij hfaces b

end ThomGame.Construction
