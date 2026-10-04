module

public import ThomGame.Construction.WheelReplacementState

/-!
# Finite normalization of one actual stellar rim index

Strong induction on the number of nonfacial components repeatedly
applies the proved decreasing replacement to its actual output graph.
The terminal graph has all rims of the chosen index facial, keeps the
original size and minimal odd state, and preserves every other index
whose rims were already facial.
-/

@[expose] public section
namespace ThomGame.Construction.SigmaMinimalState

variable {H : SigmaGraph [] []} (h : SigmaMinimalState H) [IsEmpty H.Joint]

include h in
theorem exists_facial_replacement (i : WheelCycleIndex) (hi : i ≠ oddWheelCycle) :
    ∃ K : SigmaGraph [] [], IsEmpty K.Joint ∧ SigmaMinimalState K ∧
      Fintype.card K.Hub = Fintype.card H.Hub ∧ SigmaRimsFacial K i ∧
      ∀ j : WheelCycleIndex, i ≠ j → SigmaRimsFacial H j → SigmaRimsFacial K j := by
  classical
  generalize hn : sigmaNonfacialRimCount H i = n
  induction n using Nat.strong_induction_on generalizing H with
  | h n ih =>
    by_cases hf : SigmaRimsFacial H i
    · exact ⟨H, inferInstance, h, rfl, hf, fun _ _ hj => hj⟩
    · obtain ⟨a, ha⟩ := not_forall.mp hf
      obtain ⟨K, hJ, hK, hsize, hlt, hfaces⟩ := h.exists_decreasing_replacement i a hi ha
      let : IsEmpty K.Joint := hJ
      rw [hn] at hlt
      obtain ⟨L, hLJ, hL, hLsize, hLi, hLfaces⟩ := ih _ hlt hK rfl
      exact ⟨L, hLJ, hL, hLsize.trans hsize, hLi,
        fun j hij hj => hLfaces j hij (hfaces j hij hj)⟩

end ThomGame.Construction.SigmaMinimalState
