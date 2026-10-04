module

public import ThomGame.Construction.WheelPrimaryCircuitFaces
public import ThomGame.Pictures.ExteriorNonfacialDescent

/-!
# The actual sun replacement strictly lowers the primary nonfacial count

For the selected nonfacial rim in a smoothed Sigma diagram, every new
nonfacial primary circuit has a complementary-region preimage. The
general component injection omits the selected old component and gives
strict descent on the actual normalized and smoothed output graph.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures PortGraph

noncomputable def sigmaNonfacialRimCount (H : SigmaGraph [] []) (i : WheelCycleIndex) : Nat :=
  H.nonfacialRimCount (numberedWheelCycles i) (by simp) (by simp)

def SigmaRimsFacial (H : SigmaGraph [] []) (i : WheelCycleIndex) : Prop :=
  ∀ a : H.RimDart (numberedWheelCycles i), ∃ side, (closedSigmaRimCircuit H i a).BoundsFaceOrbit side

variable {d : SigmaDiagram [] []} {H : SigmaGraph [] []} 
  (t : SigmaGraphWitness d H)

include t in
theorem sigmaNonfacialRimCount_eq_zero_iff (i : WheelCycleIndex) :
    sigmaNonfacialRimCount H i = 0 ↔ SigmaRimsFacial H i :=
  H.nonfacialRimCount_eq_zero_iff (numberedWheelCycles i) (by simp) (by simp)
    (t.dualEuler)

variable [IsEmpty H.Joint] (i : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles i)) (s : Bool)
  {w : List (Fin (wheelCycles i).length ⊕ Fin (wheelCycles i).length)}
  {K : PortGraph (sunPresentation (wheelCycles i).length (fun _ => 0)) [] w}
  (L : IncludedWheelSun i K ((closedSigmaRimCircuit H i a).frontierWord (!s)).reverse)

theorem includedSunOrientedGluing_nonfacial_count_lt
    (hn : ¬ ∃ side, (closedSigmaRimCircuit H i a).BoundsFaceOrbit side) :
    sigmaNonfacialRimCount (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!s))).graph i <
      sigmaNonfacialRimCount H i := by
  exact (closedSigmaRimCircuit H i a).nonfacialRimCount_lt_of_exterior_preimages (numberedWheelCycles i)
    (H.rimSimpleCircuit_rim (numberedWheelCycles i) (by simp) (by simp) a) hn
    (t.dualEuler) (!s)
    (L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!s)))
    ((L.orientedGlue (smoothedSigmaRimRegionGraph t i a (!s))).graph.dualEuler_eq_twice_components
      (includedSunOrientedGluing_euler t i a s L))
    (fun C hlabels hnf =>
      (includedSunOrientedGluing_primary_facial_or_exterior t i a s L C hlabels).resolve_left hnf)

end ThomGame.Construction
