module

public import ThomGame.Construction.WheelAllFacialCovers
public import ThomGame.Pictures.RimTotalCount

/-!
# The maximum rim count in the actual facial-cover character class

Lemma 11.9 chooses a maximum among same-size, character-equivalent
pictures with all constellation rims facial covers. A finite bound on
the actual component count supplies this maximum among genuine Euler
graphs. No copy property or surgery improvement is assumed.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures PortGraph RibbonConnectivity
open scoped Classical

structure SigmaMaximalRimState (H : SigmaGraph [] []) : Prop where
  euler : eulerDefect H.pairing.perm H.circuitStep = 0
  covers : ∀ j : WheelCycleIndex, SigmaRimsFacialCovers H j
  maximal : ∀ K : SigmaGraph [] [], IsEmpty K.Joint →
    eulerDefect K.pairing.perm K.circuitStep = 0 → K.character = H.character →
    Fintype.card K.Hub = Fintype.card H.Hub →
    (∀ j : WheelCycleIndex, SigmaRimsFacialCovers K j) →
      K.totalRimCount numberedWheelCycles ≤ H.totalRimCount numberedWheelCycles

variable {H : SigmaGraph [] []} [IsEmpty H.Joint]

theorem exists_maximal_rim_state
    (he : eulerDefect H.pairing.perm H.circuitStep = 0)
    (hf : ∀ j : WheelCycleIndex, SigmaRimsFacialCovers H j) :
    ∃ K : SigmaGraph [] [], IsEmpty K.Joint ∧ SigmaMaximalRimState K ∧
      K.character = H.character ∧ K.sign = H.sign ∧ Fintype.card K.Hub = Fintype.card H.Hub := by
  let B := Fintype.card WheelCycleIndex * Fintype.card H.Hub
  let Q (n : Nat) : Prop := ∃ K : SigmaGraph [] [], IsEmpty K.Joint ∧
    eulerDefect K.pairing.perm K.circuitStep = 0 ∧ K.character = H.character ∧
    Fintype.card K.Hub = Fintype.card H.Hub ∧
    (∀ j : WheelCycleIndex, SigmaRimsFacialCovers K j) ∧ K.totalRimCount numberedWheelCycles + n = B
  have hbound := H.totalRimCount_le_hubs numberedWheelCycles
  have hex : ∃ n, Q n := ⟨B - H.totalRimCount numberedWheelCycles, H, inferInstance, he, rfl, rfl,
    hf, by dsimp [B]; omega⟩
  obtain ⟨K, hJ, hKe, hKc, hKs, hKf, hKn⟩ := Nat.find_spec hex
  have hm : ∀ L : SigmaGraph [] [], IsEmpty L.Joint →
      eulerDefect L.pairing.perm L.circuitStep = 0 → L.character = K.character →
      Fintype.card L.Hub = Fintype.card K.Hub →
      (∀ j : WheelCycleIndex, SigmaRimsFacialCovers L j) →
        L.totalRimCount numberedWheelCycles ≤ K.totalRimCount numberedWheelCycles := by
    intro L hLJ hLe hLc hLs hLf
    let : IsEmpty L.Joint := hLJ
    have hb : L.totalRimCount numberedWheelCycles ≤ B := by
      have hb := L.totalRimCount_le_hubs numberedWheelCycles
      rw [hLs, hKs] at hb
      exact hb
    have hq : Q (B - L.totalRimCount numberedWheelCycles) :=
      ⟨L, hLJ, hLe, hLc.trans hKc, hLs.trans hKs, hLf, by omega⟩
    have hmin := Nat.find_min' hex hq
    omega
  exact ⟨K, hJ, ⟨hKe, hKf, hm⟩, hKc, sign_eq_of_character hKc, hKs⟩

theorem J_sigma_eq_one_iff_maximal_rim_state :
    J_sigma = 1 ↔ ∃ H : SigmaGraph [] [], IsEmpty H.Joint ∧ SigmaMaximalRimState H ∧ H.sign = 1 := by
  constructor
  · intro hj
    obtain ⟨H, hJ, hE, hs, hf⟩ := J_sigma_eq_one_iff_all_facial_covers.mp hj
    let : IsEmpty H.Joint := hJ
    obtain ⟨K, hKJ, hK, _, hKs, _⟩ := exists_maximal_rim_state hE hf
    exact ⟨K, hKJ, hK, hKs.trans hs⟩
  · rintro ⟨H, hJ, hH, hs⟩
    exact J_sigma_eq_one_iff_all_facial_covers.mpr ⟨H, hJ, hH.euler, hs, hH.covers⟩

end ThomGame.Construction
