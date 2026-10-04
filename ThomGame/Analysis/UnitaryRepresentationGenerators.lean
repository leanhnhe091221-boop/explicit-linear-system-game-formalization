module

public import ThomGame.Analysis.UnitaryRepresentationCommutants

/-! # The actual representation commutant is determined by subgroup generators -/

@[expose] public section
namespace ThomGame.Analysis

variable {R G α : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R] [Group G]

theorem unitaryRepresentationCommutant_eq_generatorCommutant (φ : G →* unitary R)
    (H : Subgroup G) (s : α → G) (hgen : Subgroup.closure (Set.range s) = H) :
    unitaryRepresentationCommutant φ H =
      StarSubalgebra.centralizer ℂ (Set.range (fun j => (φ (s j)).val)) := by
  ext x
  rw [unitaryRepresentationCommutant_mem_iff, unitaryRangeCommutant_mem_iff]
  constructor
  · intro h j
    apply h (s j)
    rw [← hgen]
    exact Subgroup.subset_closure ⟨j, rfl⟩
  · intro h g hg
    have hK : Subgroup.closure (Set.range s) ≤ (unitaryCommutingSubgroup x).comap φ := by
      apply (Subgroup.closure_le _).mpr
      rintro z ⟨j, rfl⟩
      exact h j
    rw [hgen] at hK
    exact hK hg

end ThomGame.Analysis
