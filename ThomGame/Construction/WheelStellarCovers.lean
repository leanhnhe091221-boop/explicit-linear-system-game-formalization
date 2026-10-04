module

public import ThomGame.Construction.WheelConstellationNormalization
public import ThomGame.Pictures.RowFacialCovers

/-!
# All stellar rims of the actual normalized Sigma graph are facial covers

The label-cover conclusion follows from genuine cancellation in a
minimal odd row graph. It adds no hypothesis to stellar normalization.
The exceptional nonstellar pentagon, covers-to-copies step and wheel
collapse remain separate parts of the embedding proof.
-/

@[expose] public section
namespace ThomGame.Construction

def SigmaRimsFacialCovers (H : SigmaGraph [] []) (i : WheelCycleIndex) : Prop :=
  ∀ a : H.RimDart (numberedWheelCycles i),
    (∃ side, (closedSigmaRimCircuit H i a).BoundsFaceOrbit side) ∧
      (closedSigmaRimCircuit H i a).IsLabelCover

namespace SigmaMinimalState

variable {H : SigmaGraph [] []} (h : SigmaMinimalState H) [IsEmpty H.Joint]

include h in
theorem facial_covers_of_facial (i : WheelCycleIndex) (hf : SigmaRimsFacial H i) :
    SigmaRimsFacialCovers H i := by
  intro a
  exact ⟨hf a, Pictures.PortGraph.ClosedMinimalOddState.rim_isLabelCover_of_facial
    (numberedWheelCycles i) a h (hf a)⟩

include h in
theorem exists_stellar_facial_covers :
    ∃ K : SigmaGraph [] [], IsEmpty K.Joint ∧ SigmaMinimalState K ∧
      Fintype.card K.Hub = Fintype.card H.Hub ∧
      ∀ i : WheelCycleIndex, i ≠ oddWheelCycle → SigmaRimsFacialCovers K i := by
  obtain ⟨K, hJ, hK, hsize, hfaces⟩ := h.exists_stellar_normalization
  let : IsEmpty K.Joint := hJ
  exact ⟨K, hJ, hK, hsize, fun i hi => hK.facial_covers_of_facial i (hfaces i hi)⟩

end SigmaMinimalState

theorem J_sigma_eq_one_iff_stellar_facial_covers :
    J_sigma = 1 ↔ ∃ H : SigmaGraph [] [], IsEmpty H.Joint ∧ SigmaMinimalState H ∧
      ∀ i : WheelCycleIndex, i ≠ oddWheelCycle → SigmaRimsFacialCovers H i := by
  constructor
  · intro hj
    obtain ⟨H, hJ, h⟩ := J_sigma_eq_one_iff_closed_minimal_state.mp hj
    let : IsEmpty H.Joint := hJ
    obtain ⟨K, hKJ, hK, _, hf⟩ := h.exists_stellar_facial_covers
    exact ⟨K, hKJ, hK, hf⟩
  · rintro ⟨H, hJ, h, _⟩
    exact J_sigma_eq_one_iff_closed_minimal_state.mpr ⟨H, hJ, h⟩

end ThomGame.Construction
