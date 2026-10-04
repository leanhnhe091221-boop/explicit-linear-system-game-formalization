module

public import ThomGame.Analysis.IntegerLatticeShearCalculus
public import ThomGame.Analysis.HilbertVectorMeasureCovariance
public import ThomGame.Analysis.IntegerTorusMeasureCriterion

/-! Exact shear pushforward and quantitative measure bounds for lattice representations. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open IntegerTorus MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem latticeSpectralMeasure_shear_map (ρ : IntegerPlane.Group →* (H ≃ₗᵢ[ℂ] H))
    (S : H ≃ₗᵢ[ℂ] H) (b : Bool)
    (hS : ∀ v : IntegerPlane.Group, S * ρ v * S⁻¹ = ρ (IntegerPlane.shear b v)) (ξ : H) :
    (latticeSpectralMeasure ρ (S ξ)).map (integerShear b 1) = latticeSpectralMeasure ρ ξ :=
  hilbertVectorMeasure_map_of_covariant (latticeUnitaryPair ρ).calculus S (integerShear b 1)
    (latticeCalculus_shear_covariant ρ S b hS) ξ

theorem latticeSpectralMeasure_shear_image (ρ : IntegerPlane.Group →* (H ≃ₗᵢ[ℂ] H))
    (S : H ≃ₗᵢ[ℂ] H) (b : Bool)
    (hS : ∀ v : IntegerPlane.Group, S * ρ v * S⁻¹ = ρ (IntegerPlane.shear b v))
    (ξ : H) (s : Set Torus) (hs : MeasurableSet s) :
    (latticeSpectralMeasure ρ (S ξ)).real s =
      (latticeSpectralMeasure ρ ξ).real (integerShear b 1 '' s) :=
  hilbertVectorMeasure_image_of_covariant (latticeUnitaryPair ρ).calculus S (integerShear b 1)
    (latticeCalculus_shear_covariant ρ S b hS) ξ s hs

theorem latticeSpectralMeasure_shear_bound (ρ : IntegerPlane.Group →* (H ≃ₗᵢ[ℂ] H))
    (S : H ≃ₗᵢ[ℂ] H) (b : Bool)
    (hS : ∀ v : IntegerPlane.Group, S * ρ v * S⁻¹ = ρ (IntegerPlane.shear b v))
    (ξ : H) (hξ : ‖ξ‖ = 1) (s : Set Torus) (hs : MeasurableSet s) :
    (latticeSpectralMeasure ρ ξ).real s ≤
      (latticeSpectralMeasure ρ ξ).real (integerShear b 1 '' s) + 2 * ‖S ξ - ξ‖ :=
  hilbertVectorMeasure_shear_bound_of_covariant (latticeUnitaryPair ρ).calculus S (integerShear b 1)
    (latticeCalculus_shear_covariant ρ S b hS) ξ hξ s hs

theorem latticeShear_no_small_unit_vector (ρ : IntegerPlane.Group →* (H ≃ₗᵢ[ℂ] H))
    (S : Bool → H ≃ₗᵢ[ℂ] H)
    (hS : ∀ (b : Bool) (v : IntegerPlane.Group), S b * ρ v * (S b)⁻¹ = ρ (IntegerPlane.shear b v))
    (ξ : H) (hξ : ‖ξ‖ = 1) (horth : ξ ∈ (hilbertUnitaryInvariants ρ)ᗮ)
    (hlattice : ∀ b : Bool, ‖ρ (latticeGenerator b) ξ - ξ‖ ≤ 1 / 100)
    (hshear : ∀ b : Bool, ‖S b ξ - ξ‖ ≤ 1 / 100) : False := by
  let := latticeSpectralMeasure_probability ρ ξ hξ
  apply no_almost_invariant_measure (latticeSpectralMeasure ρ ξ) (1 / 100) (by norm_num) le_rfl
    (latticeSpectralMeasure_origin_null ρ ξ horth) _ (latticeSpectralMeasure_energy_le ρ ξ _ hlattice)
  intro b s hs
  exact (latticeSpectralMeasure_shear_bound ρ (S b) b (hS b) ξ hξ s hs).trans
    (by linarith [hshear b])

end ThomGame.Analysis
