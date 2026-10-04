module

public import ThomGame.Analysis.CommutingUnitarySpectralOrigin
public import ThomGame.Analysis.HilbertVectorMeasurePerturbation
public import ThomGame.Analysis.HilbertUnitaryInvariants
public import ThomGame.Groups.IntegerPlaneShearAction

/-! Joint spectral measures for actual unitary representations of the integer lattice. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open IntegerTorus MeasureTheory

def latticeGenerator (b : Bool) : IntegerPlane.Group :=
  Multiplicative.ofAdd (if b then (0, 1) else (1, 0))

theorem lattice_generator_decomposition (v : IntegerPlane.Group) :
    v = latticeGenerator false ^ v.toAdd.1 * latticeGenerator true ^ v.toAdd.2 := by
  apply Multiplicative.toAdd.injective
  change v.toAdd = v.toAdd.1 • (1, 0) + v.toAdd.2 • (0, 1)
  ext <;> simp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def latticeUnitaryPair (ρ : IntegerPlane.Group →* (H ≃ₗᵢ[ℂ] H)) :
    CommutingUnitaryPair (H →L[ℂ] H) :=
  CommutingUnitaryPair.ofIsometries (ρ (latticeGenerator false)) (ρ (latticeGenerator true))
    ((Commute.all (latticeGenerator false) (latticeGenerator true)).map ρ)

theorem latticeUnitaryPair_commonFixed (ρ : IntegerPlane.Group →* (H ≃ₗᵢ[ℂ] H)) :
    (latticeUnitaryPair ρ).commonFixed = hilbertUnitaryInvariants ρ := by
  ext ξ
  constructor
  · rintro ⟨h₀, h₁⟩
    have hg₀ : latticeGenerator false ∈ hilbertVectorStabilizer ρ ξ := h₀
    have hg₁ : latticeGenerator true ∈ hilbertVectorStabilizer ρ ξ := h₁
    intro g
    change g ∈ hilbertVectorStabilizer ρ ξ
    rw [lattice_generator_decomposition g]
    exact (hilbertVectorStabilizer ρ ξ).mul_mem
      ((hilbertVectorStabilizer ρ ξ).zpow_mem hg₀ _)
      ((hilbertVectorStabilizer ρ ξ).zpow_mem hg₁ _)
  · intro hξ
    exact ⟨hξ (latticeGenerator false), hξ (latticeGenerator true)⟩

def latticeSpectralMeasure (ρ : IntegerPlane.Group →* (H ≃ₗᵢ[ℂ] H)) (ξ : H) : Measure Torus :=
  (latticeUnitaryPair ρ).spectralMeasure ξ

instance latticeSpectralMeasure_finite (ρ : IntegerPlane.Group →* (H ≃ₗᵢ[ℂ] H)) (ξ : H) :
    IsFiniteMeasure (latticeSpectralMeasure ρ ξ) :=
  inferInstanceAs (IsFiniteMeasure ((latticeUnitaryPair ρ).spectralMeasure ξ))

instance latticeSpectralMeasure_regular (ρ : IntegerPlane.Group →* (H ≃ₗᵢ[ℂ] H)) (ξ : H) :
    (latticeSpectralMeasure ρ ξ).Regular :=
  inferInstanceAs ((latticeUnitaryPair ρ).spectralMeasure ξ).Regular

theorem latticeSpectralMeasure_probability (ρ : IntegerPlane.Group →* (H ≃ₗᵢ[ℂ] H)) (ξ : H)
    (hξ : ‖ξ‖ = 1) : IsProbabilityMeasure (latticeSpectralMeasure ρ ξ) :=
  (latticeUnitaryPair ρ).spectralMeasure_probability ξ hξ

theorem latticeSpectralMeasure_origin_null (ρ : IntegerPlane.Group →* (H ≃ₗᵢ[ℂ] H)) (ξ : H)
    (hξ : ξ ∈ (hilbertUnitaryInvariants ρ)ᗮ) :
    (latticeSpectralMeasure ρ ξ).real {(0 : Torus)} = 0 := by
  apply (latticeUnitaryPair ρ).spectralMeasure_origin_null ξ
  rwa [latticeUnitaryPair_commonFixed]

theorem latticeSpectralMeasure_energy (ρ : IntegerPlane.Group →* (H ≃ₗᵢ[ℂ] H)) (ξ : H) :
    (∫ z, coordinateEnergy z ∂latticeSpectralMeasure ρ ξ) =
      ‖ρ (latticeGenerator false) ξ - ξ‖ ^ 2 + ‖ρ (latticeGenerator true) ξ - ξ‖ ^ 2 :=
  (latticeUnitaryPair ρ).spectralMeasure_energy ξ

theorem latticeSpectralMeasure_energy_le (ρ : IntegerPlane.Group →* (H ≃ₗᵢ[ℂ] H)) (ξ : H) (ε : ℝ)
    (hmove : ∀ b : Bool, ‖ρ (latticeGenerator b) ξ - ξ‖ ≤ ε) :
    (∫ z, coordinateEnergy z ∂latticeSpectralMeasure ρ ξ) ≤ 2 * ε ^ 2 :=
  (latticeUnitaryPair ρ).spectralMeasure_energy_le ξ ε (hmove false) (hmove true)

theorem latticeSpectralMeasure_borel_perturbation (ρ : IntegerPlane.Group →* (H ≃ₗᵢ[ℂ] H))
    (ξ η : H) (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1) (s : Set Torus) (hs : MeasurableSet s) :
    |(latticeSpectralMeasure ρ ξ).real s - (latticeSpectralMeasure ρ η).real s| ≤ 2 * ‖ξ - η‖ :=
  hilbertVectorMeasure_unit_borel_sub_abs_le (latticeUnitaryPair ρ).calculus ξ η hξ hη s hs

end ThomGame.Analysis
