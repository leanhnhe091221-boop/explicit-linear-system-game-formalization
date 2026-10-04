module

public import ThomGame.Analysis.IntegralShearRootPlaneKazhdan
public import ThomGame.Analysis.IntegerPlaneUniformDisplacement

/-! Uniform control of all integer roots using the actual free-shear maps. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open Compressor IntegralShear

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem rootPlane_pullback_lattice (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (r : Root) :
    freeShearLatticeRepresentation (ρ.comp (rootPlaneSemidirectHom r)) =
      ρ.comp (rootPlaneHom r) := by
  apply MonoidHom.ext
  intro v
  change ρ (rootPlaneSemidirectHom r (SemidirectProduct.inl v)) = ρ (rootPlaneHom r v)
  rw [rootPlaneSemidirectHom_inl]

variable [CompleteSpace H]

theorem rootPlane_invariant_distance (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (r : Root)
    (ξ : H) (ε : ℝ)
    (hmove : ∀ i : Bool × Bool, ‖ρ (rootPlaneKazhdanGenerator r i) ξ - ξ‖ ≤ ε) :
    ‖ξ - (hilbertUnitaryInvariants (ρ.comp (rootPlaneHom r))).starProjection ξ‖ ≤ 100 * ε := by
  have h := freeShear_invariant_distance (ρ.comp (rootPlaneSemidirectHom r)) ξ ε (by
    intro i
    simpa only [MonoidHom.comp_apply, rootPlaneSemidirectHom_generator] using hmove i)
  rwa [rootPlane_pullback_lattice] at h

theorem rootPlane_close_invariant (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (r : Root)
    (ξ : H) (ε : ℝ)
    (hmove : ∀ i : Bool × Bool, ‖ρ (rootPlaneKazhdanGenerator r i) ξ - ξ‖ ≤ ε) :
    ∃ η ∈ hilbertUnitaryInvariants (ρ.comp (rootPlaneHom r)), ‖ξ - η‖ ≤ 100 * ε :=
  ⟨_, (hilbertUnitaryInvariants (ρ.comp (rootPlaneHom r))).starProjection_apply_mem ξ,
    rootPlane_invariant_distance ρ r ξ ε hmove⟩

theorem rootPlane_uniform_displacement (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (r : Root)
    (ξ : H) (ε : ℝ)
    (hmove : ∀ i : Bool × Bool, ‖ρ (rootPlaneKazhdanGenerator r i) ξ - ξ‖ ≤ ε)
    (v : IntegerPlane.Group) : ‖ρ (rootPlaneHom r v) ξ - ξ‖ ≤ 200 * ε := by
  have h := freeShear_lattice_uniform_displacement (ρ.comp (rootPlaneSemidirectHom r)) ξ ε (by
    intro i
    simpa only [MonoidHom.comp_apply, rootPlaneSemidirectHom_generator] using hmove i) v
  simpa only [rootPlane_pullback_lattice, MonoidHom.comp_apply] using h

theorem rootPlaneKazhdanGenerator_is_root (r : Root) (i : Bool × Bool) :
    ∃ s : Root, rootPlaneKazhdanGenerator r i = of s := by
  rcases i with ⟨a, b⟩
  cases a <;> cases b <;> simp [rootPlaneKazhdanGenerator]

theorem integralShear_root_uniform_displacement (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H))
    (ξ : H) (ε : ℝ) (hmove : ∀ s : Root, ‖ρ (of s) ξ - ξ‖ ≤ ε)
    (r : Root) (m : ℤ) : ‖ρ (rootElement r m) ξ - ξ‖ ≤ 200 * ε := by
  have ha : across (across r) = r := by revert r; decide +kernel
  have h := rootPlane_uniform_displacement ρ (across r) ξ ε (by
    intro i
    obtain ⟨s, hs⟩ := rootPlaneKazhdanGenerator_is_root (across r) i
    rw [hs]
    exact hmove s) (Multiplicative.ofAdd (m, 0))
  change ‖ρ (rootElement (across (across r)) m * rootElement (right (across r)) 0) ξ - ξ‖ ≤ _ at h
  simpa only [ha, rootElement_zero, mul_one] using h

end ThomGame.Analysis
