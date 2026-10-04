module

public import ThomGame.Construction.WheelRimNormalization

/-!
# All stellar indices become facial on the actual Sigma graph

Finite-set induction normalizes one additional index while preserving
every previously facial index. Applying this to all indices except the
unique nonstellar pentagon gives the closed minimal odd Sigma instance
of stellar constellation normalization. The exceptional index and the
subsequent wheel collapse are separate steps.
-/

@[expose] public section
namespace ThomGame.Construction

namespace SigmaMinimalState

variable {H : SigmaGraph [] []} (h : SigmaMinimalState H) [IsEmpty H.Joint]

include h in
theorem exists_facial_on (I : Finset WheelCycleIndex)
    (hI : ∀ i ∈ I, i ≠ oddWheelCycle) :
    ∃ K : SigmaGraph [] [], IsEmpty K.Joint ∧ SigmaMinimalState K ∧
      Fintype.card K.Hub = Fintype.card H.Hub ∧
      (∀ i ∈ I, SigmaRimsFacial K i) ∧
      ∀ j, j ∉ I → SigmaRimsFacial H j → SigmaRimsFacial K j := by
  classical
  revert hI
  induction I using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨H, inferInstance, h, rfl, by simp, fun _ _ hj => hj⟩
  | @insert i I hi ih =>
    intro hI
    have hI' : ∀ j ∈ I, j ≠ oddWheelCycle :=
      fun j hj => hI j (Finset.mem_insert_of_mem hj)
    obtain ⟨K, hJ, hK, hsize, hfaces, hpres⟩ := ih hI'
    let : IsEmpty K.Joint := hJ
    obtain ⟨L, hLJ, hL, hLsize, hLi, hLpres⟩ :=
      hK.exists_facial_replacement i (hI i (Finset.mem_insert_self i I))
    refine ⟨L, hLJ, hL, hLsize.trans hsize, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hLi
      · have hij : i ≠ j := by
          intro he
          subst j
          exact hi hj
        exact hLpres j hij (hfaces j hj)
    · intro j hj hjface
      have hj' : j ≠ i ∧ j ∉ I := by simpa only [Finset.mem_insert, not_or] using hj
      exact hLpres j hj'.1.symm (hpres j hj'.2 hjface)

include h in
theorem exists_stellar_normalization :
    ∃ K : SigmaGraph [] [], IsEmpty K.Joint ∧ SigmaMinimalState K ∧
      Fintype.card K.Hub = Fintype.card H.Hub ∧
      ∀ i : WheelCycleIndex, i ≠ oddWheelCycle → SigmaRimsFacial K i := by
  classical
  obtain ⟨K, hJ, hK, hsize, hfaces, _⟩ :=
    h.exists_facial_on (Finset.univ.erase oddWheelCycle)
      (fun _ hi => (Finset.mem_erase.mp hi).1)
  exact ⟨K, hJ, hK, hsize, fun i hi => hfaces i (by simp [hi])⟩

end SigmaMinimalState

theorem J_sigma_eq_one_iff_stellar_normalized_state :
    J_sigma = 1 ↔ ∃ H : SigmaGraph [] [], IsEmpty H.Joint ∧ SigmaMinimalState H ∧
      ∀ i : WheelCycleIndex, i ≠ oddWheelCycle → SigmaRimsFacial H i := by
  constructor
  · intro hj
    obtain ⟨H, hJ, h⟩ := J_sigma_eq_one_iff_closed_minimal_state.mp hj
    let : IsEmpty H.Joint := hJ
    obtain ⟨K, hKJ, hK, _, hf⟩ := h.exists_stellar_normalization
    exact ⟨K, hKJ, hK, hf⟩
  · rintro ⟨H, hJ, h, _⟩
    exact J_sigma_eq_one_iff_closed_minimal_state.mpr ⟨H, hJ, h⟩

end ThomGame.Construction
