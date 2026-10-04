module

public import ThomGame.Construction.WheelOddPathNormalization

/-!
# The new character-class minimum after exceptional-path normalization

The paper chooses a new minimum after Figure 19(b), because insertion
increases size. The comparison class consists of actual Euler-saturated,
joint-free graphs with the same full character and the proved rim
alternatives. No faciality of the independent-only rims is assumed.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

variable {R S : Type*} [Fintype R] {P : InvolutionPresentation R S} {u v : List S}
  {G H : PortGraph P u v}

theorem sign_eq_of_character (h : G.character = H.character) : G.sign = H.sign := by
  rw [G.sign_eq_character, H.sign_eq_character, h]

end ThomGame.Pictures.PortGraph

namespace ThomGame.Construction

open Pictures PortGraph RibbonConnectivity
open scoped Classical

def SigmaRimPrepared (H : SigmaGraph [] []) : Prop :=
  (∀ i : WheelCycleIndex, i ≠ oddWheelCycle → SigmaRimsFacialCovers H i) ∧
  ∀ a : H.RimDart (numberedWheelCycles oddWheelCycle),
    ((∃ side, (closedSigmaRimCircuit H oddWheelCycle a).BoundsFaceOrbit side) ∧
      (closedSigmaRimCircuit H oddWheelCycle a).IsLabelCover) ∨ OddRimIndependentOnly H a

structure SigmaCharacterMinimalRimState (H : SigmaGraph [] []) : Prop where
  euler : eulerDefect H.pairing.perm H.circuitStep = 0
  prepared : SigmaRimPrepared H
  minimal : ∀ K : SigmaGraph [] [], IsEmpty K.Joint →
    eulerDefect K.pairing.perm K.circuitStep = 0 → K.character = H.character → SigmaRimPrepared K →
      Fintype.card H.Hub ≤ Fintype.card K.Hub

variable {H : SigmaGraph [] []} [IsEmpty H.Joint]

theorem exists_character_minimum_of_prepared
    (he : eulerDefect H.pairing.perm H.circuitStep = 0) (hp : SigmaRimPrepared H) :
    ∃ K : SigmaGraph [] [], IsEmpty K.Joint ∧ SigmaCharacterMinimalRimState K ∧
      K.character = H.character ∧ K.sign = H.sign ∧ Fintype.card K.Hub ≤ Fintype.card H.Hub := by
  let Q (n : Nat) : Prop := ∃ K : SigmaGraph [] [], IsEmpty K.Joint ∧
    eulerDefect K.pairing.perm K.circuitStep = 0 ∧ K.character = H.character ∧
      SigmaRimPrepared K ∧ Fintype.card K.Hub = n
  have hex : ∃ n, Q n := ⟨Fintype.card H.Hub, H, inferInstance, he, rfl, hp, rfl⟩
  obtain ⟨K, hKJ, hKe, hKc, hKp, hKn⟩ := Nat.find_spec hex
  have hmin : ∀ L : SigmaGraph [] [], IsEmpty L.Joint →
      eulerDefect L.pairing.perm L.circuitStep = 0 → L.character = K.character → SigmaRimPrepared L →
        Fintype.card K.Hub ≤ Fintype.card L.Hub := by
    intro L hLJ hLe hLc hLp
    have hq : Q (Fintype.card L.Hub) := ⟨L, hLJ, hLe, hLc.trans hKc, hLp, rfl⟩
    exact hKn.trans_le (Nat.find_min' hex hq)
  exact ⟨K, hKJ, ⟨hKe, hKp, hmin⟩, hKc, sign_eq_of_character hKc,
    hmin H inferInstance he hKc.symm hp⟩

theorem exists_character_minimal_rim_state
    (he : eulerDefect H.pairing.perm H.circuitStep = 0)
    (hf : ∀ i : WheelCycleIndex, i ≠ oddWheelCycle → SigmaRimsFacialCovers H i) :
    ∃ K : SigmaGraph [] [], IsEmpty K.Joint ∧ SigmaCharacterMinimalRimState K ∧
      K.character = H.character ∧ K.sign = H.sign ∧
      Fintype.card K.Hub ≤ Fintype.card H.Hub + 2 * oddUnfinishedPathCount H := by
  obtain ⟨G, hGJ, hGe, hGc, hGs, hGf, hGi, hGb⟩ := exists_odd_rim_normalization he hf
  let : IsEmpty G.Joint := hGJ
  obtain ⟨K, hKJ, hK, hKc, hKs, hKb⟩ := exists_character_minimum_of_prepared hGe ⟨hGf, hGi⟩
  exact ⟨K, hKJ, hK, hKc.trans hGc, hKs.trans hGs, hKb.trans hGb⟩

theorem J_sigma_eq_one_iff_character_minimal_rim_state :
    J_sigma = 1 ↔ ∃ H : SigmaGraph [] [], IsEmpty H.Joint ∧ SigmaCharacterMinimalRimState H ∧ H.sign = 1 := by
  constructor
  · intro hj
    obtain ⟨H, hJ, hH, hf⟩ := J_sigma_eq_one_iff_stellar_facial_covers.mp hj
    let : IsEmpty H.Joint := hJ
    obtain ⟨K, hKJ, hK, _, hs, _⟩ := exists_character_minimal_rim_state hH.euler hf
    exact ⟨K, hKJ, hK, hs.trans hH.sign⟩
  · rintro ⟨H, hJ, hH, hs⟩
    obtain ⟨d, _, _, hd⟩ := H.exists_closed_diagram_of_saturated_preserving
      (fun _ => by change 0 < 3; decide +kernel) (H.rotationEuler_saturated_iff.mpr hH.euler)
    obtain ⟨e, he, hmin⟩ := d.exists_minimal
    exact J_sigma_eq_one_iff_closed_minimal_odd_diagram.mpr ⟨e, he.trans (hd.trans hs), hmin⟩

end ThomGame.Construction
