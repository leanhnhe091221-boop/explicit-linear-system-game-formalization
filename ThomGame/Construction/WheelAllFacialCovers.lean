module

public import ThomGame.Construction.WheelOddErasurePrepared

/-!
# The actual Sigma constellation has a character-equivalent facial-cover form

A pure-independent rim would erase to a strictly smaller Euler graph
in the same full character class, with every prepared rim condition
preserved. It therefore contradicts the new minimum taken after path
insertion. All constellation rims are facial covers in that minimum.
Turning closed covers into copies and collapsing wheels remain separate.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures PortGraph RibbonConnectivity
open scoped Classical

namespace SigmaCharacterMinimalRimState

variable {H : SigmaGraph [] []} [IsEmpty H.Joint] (h : SigmaCharacterMinimalRimState H)

include h in
theorem no_independent_rim (a : H.RimDart (numberedWheelCycles oddWheelCycle)) :
    ¬ OddRimIndependentOnly H a := by
  intro hi
  obtain ⟨K, circles, ⟨t⟩, hJ, hEuler, hchar, _, _, hlt⟩ := exists_oddIndependent_erasure a hi h.euler
  let : IsEmpty K.Joint := hJ
  have hp := oddIndependentErasure_prepared a hi t h.euler h.prepared
  exact (Nat.not_le_of_lt hlt) (h.minimal K hJ hEuler hchar hp)

include h in
theorem all_facial_covers (j : WheelCycleIndex) : SigmaRimsFacialCovers H j := by
  by_cases hj : j = oddWheelCycle
  · subst j
    intro a
    rcases h.prepared.2 a with hf | hi
    · exact hf
    · exact (h.no_independent_rim a hi).elim
  · exact h.prepared.1 j hj

end SigmaCharacterMinimalRimState

variable {H : SigmaGraph [] []} [IsEmpty H.Joint]

theorem exists_all_facial_covers
    (he : eulerDefect H.pairing.perm H.circuitStep = 0)
    (hf : ∀ j : WheelCycleIndex, j ≠ oddWheelCycle → SigmaRimsFacialCovers H j) :
    ∃ K : SigmaGraph [] [], IsEmpty K.Joint ∧
      eulerDefect K.pairing.perm K.circuitStep = 0 ∧ K.character = H.character ∧ K.sign = H.sign ∧
      (∀ j : WheelCycleIndex, SigmaRimsFacialCovers K j) ∧
      Fintype.card K.Hub ≤ Fintype.card H.Hub + 2 * oddUnfinishedPathCount H := by
  obtain ⟨K, hJ, hK, hc, hs, hb⟩ := exists_character_minimal_rim_state he hf
  let : IsEmpty K.Joint := hJ
  exact ⟨K, hJ, hK.euler, hc, hs, hK.all_facial_covers, hb⟩

theorem J_sigma_eq_one_iff_all_facial_covers :
    J_sigma = 1 ↔ ∃ H : SigmaGraph [] [], IsEmpty H.Joint ∧
      eulerDefect H.pairing.perm H.circuitStep = 0 ∧ H.sign = 1 ∧
        ∀ j : WheelCycleIndex, SigmaRimsFacialCovers H j := by
  constructor
  · intro hj
    obtain ⟨H, hJ, hH, hs⟩ := J_sigma_eq_one_iff_character_minimal_rim_state.mp hj
    let : IsEmpty H.Joint := hJ
    exact ⟨H, hJ, hH.euler, hs, hH.all_facial_covers⟩
  · rintro ⟨H, hJ, he, hs, hf⟩
    let : IsEmpty H.Joint := hJ
    have hp : SigmaRimPrepared H := ⟨fun j _ => hf j, fun a => Or.inl (hf oddWheelCycle a)⟩
    obtain ⟨K, hKJ, hK, _, hKs, _⟩ := exists_character_minimum_of_prepared he hp
    exact J_sigma_eq_one_iff_character_minimal_rim_state.mpr ⟨K, hKJ, hK, hKs.trans hs⟩

end ThomGame.Construction
