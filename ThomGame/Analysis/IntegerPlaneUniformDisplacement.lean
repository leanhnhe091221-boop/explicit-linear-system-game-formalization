module

public import ThomGame.Analysis.IntegerPlaneRelativeKazhdan
public import ThomGame.Analysis.HilbertRelativeKazhdanProjection

/-! Uniform control of every lattice element from four almost-fixed semidirect generators. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open IntegerPlane

theorem freeShear_inl_range_normal :
    (SemidirectProduct.inl : IntegerPlane.Group →* FreeShearProduct).range.Normal := by
  rw [SemidirectProduct.range_inl_eq_ker_rightHom]
  infer_instance

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem freeShear_invariant_distance (ρ : FreeShearProduct →* (H ≃ₗᵢ[ℂ] H))
    (ξ : H) (ε : ℝ)
    (hmove : ∀ i : Bool × Bool, ‖ρ (freeShearGenerator i) ξ - ξ‖ ≤ ε) :
    ‖ξ - (hilbertUnitaryInvariants (freeShearLatticeRepresentation ρ)).starProjection ξ‖ ≤
      100 * ε := by
  let := freeShear_inl_range_normal
  have h := hilbertRelativeKazhdanBound_distance _ _ _ (by norm_num : (0 : ℝ) < 1 / 100)
    freeShear_relativeKazhdanBound ρ ξ ε (by
      intro g hg
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hg
      exact hmove i)
  have he : ε / ((1 : ℝ) / 100) = 100 * ε := by ring
  rw [he] at h
  exact h

theorem freeShear_close_invariant (ρ : FreeShearProduct →* (H ≃ₗᵢ[ℂ] H))
    (ξ : H) (ε : ℝ)
    (hmove : ∀ i : Bool × Bool, ‖ρ (freeShearGenerator i) ξ - ξ‖ ≤ ε) :
    ∃ η ∈ hilbertUnitaryInvariants (freeShearLatticeRepresentation ρ), ‖ξ - η‖ ≤ 100 * ε :=
  ⟨_, (hilbertUnitaryInvariants (freeShearLatticeRepresentation ρ)).starProjection_apply_mem ξ,
    freeShear_invariant_distance ρ ξ ε hmove⟩

theorem freeShear_lattice_uniform_displacement (ρ : FreeShearProduct →* (H ≃ₗᵢ[ℂ] H))
    (ξ : H) (ε : ℝ)
    (hmove : ∀ i : Bool × Bool, ‖ρ (freeShearGenerator i) ξ - ξ‖ ≤ ε)
    (v : IntegerPlane.Group) :
    ‖freeShearLatticeRepresentation ρ v ξ - ξ‖ ≤ 200 * ε := by
  let := freeShear_inl_range_normal
  have h := hilbertRelativeKazhdanBound_uniform_displacement _ _ _
    (by norm_num : (0 : ℝ) < 1 / 100) freeShear_relativeKazhdanBound ρ ξ ε (by
      intro g hg
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hg
      exact hmove i) v
  change ‖freeShearLatticeRepresentation ρ v ξ - ξ‖ ≤ _ at h
  convert h using 1
  ring

end ThomGame.Analysis
