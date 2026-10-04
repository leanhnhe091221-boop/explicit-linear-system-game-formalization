module

public import ThomGame.Analysis.CommutingUnitaryTorusCalculus
public import ThomGame.Analysis.HilbertVectorMeasure

/-! A genuine joint torus measure for commuting Hilbert unitaries, with exact energy formulas. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis.CommutingUnitaryPair

open MeasureTheory IntegerTorus

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def spectralMeasure (p : CommutingUnitaryPair (H →L[ℂ] H)) (ξ : H) : Measure Torus :=
  hilbertVectorMeasure p.calculus ξ

instance spectralMeasure_finite (p : CommutingUnitaryPair (H →L[ℂ] H)) (ξ : H) :
    IsFiniteMeasure (spectralMeasure p ξ) :=
  inferInstanceAs (IsFiniteMeasure (hilbertVectorMeasure p.calculus ξ))

instance spectralMeasure_regular (p : CommutingUnitaryPair (H →L[ℂ] H)) (ξ : H) :
    (spectralMeasure p ξ).Regular :=
  inferInstanceAs (hilbertVectorMeasure p.calculus ξ).Regular

theorem spectralMeasure_mass (p : CommutingUnitaryPair (H →L[ℂ] H)) (ξ : H) :
    (spectralMeasure p ξ).real Set.univ = ‖ξ‖ ^ 2 := hilbertVectorMeasure_mass p.calculus ξ

theorem spectralMeasure_probability (p : CommutingUnitaryPair (H →L[ℂ] H)) (ξ : H)
    (hξ : ‖ξ‖ = 1) : IsProbabilityMeasure (spectralMeasure p ξ) :=
  hilbertVectorMeasure_probability p.calculus ξ hξ

theorem spectralMeasure_first_energy (p : CommutingUnitaryPair (H →L[ℂ] H)) (ξ : H) :
    (∫ z, ‖character z.1 - 1‖ ^ 2 ∂spectralMeasure p ξ) =
      ‖(p.first : H →L[ℂ] H) ξ - ξ‖ ^ 2 := by
  have h := hilbertVectorMeasure_integral_normSq p.calculus ξ (coordinateCharacter false - 1)
  rw [map_sub, calculus_first, map_one] at h
  simpa [spectralMeasure, coordinateCharacter, sub_apply] using h

theorem spectralMeasure_second_energy (p : CommutingUnitaryPair (H →L[ℂ] H)) (ξ : H) :
    (∫ z, ‖character z.2 - 1‖ ^ 2 ∂spectralMeasure p ξ) =
      ‖(p.second : H →L[ℂ] H) ξ - ξ‖ ^ 2 := by
  have h := hilbertVectorMeasure_integral_normSq p.calculus ξ (coordinateCharacter true - 1)
  rw [map_sub, calculus_second, map_one] at h
  simpa [spectralMeasure, coordinateCharacter, sub_apply] using h

theorem spectralMeasure_energy (p : CommutingUnitaryPair (H →L[ℂ] H)) (ξ : H) :
    (∫ z, coordinateEnergy z ∂spectralMeasure p ξ) =
      ‖(p.first : H →L[ℂ] H) ξ - ξ‖ ^ 2 + ‖(p.second : H →L[ℂ] H) ξ - ξ‖ ^ 2 := by
  have h₁ : Continuous (fun z : Torus => ‖character z.1 - 1‖ ^ 2) :=
    ((character_continuous.comp continuous_fst).sub continuous_const).norm.pow 2
  have h₂ : Continuous (fun z : Torus => ‖character z.2 - 1‖ ^ 2) :=
    ((character_continuous.comp continuous_snd).sub continuous_const).norm.pow 2
  change (∫ z, ‖character z.1 - 1‖ ^ 2 + ‖character z.2 - 1‖ ^ 2 ∂spectralMeasure p ξ) = _
  rw [integral_add
    (h₁.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (h₂.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
    spectralMeasure_first_energy, spectralMeasure_second_energy]

theorem spectralMeasure_energy_le (p : CommutingUnitaryPair (H →L[ℂ] H)) (ξ : H) (ε : ℝ)
    (h₁ : ‖(p.first : H →L[ℂ] H) ξ - ξ‖ ≤ ε)
    (h₂ : ‖(p.second : H →L[ℂ] H) ξ - ξ‖ ≤ ε) :
    (∫ z, coordinateEnergy z ∂spectralMeasure p ξ) ≤ 2 * ε ^ 2 := by
  rw [spectralMeasure_energy]
  nlinarith [norm_nonneg ((p.first : H →L[ℂ] H) ξ - ξ),
    norm_nonneg ((p.second : H →L[ℂ] H) ξ - ξ)]

theorem ofIsometries_spectralMeasure_energy (U V : H ≃ₗᵢ[ℂ] H) (h : Commute U V) (ξ : H) :
    (∫ z, coordinateEnergy z ∂spectralMeasure (ofIsometries U V h) ξ) =
      ‖U ξ - ξ‖ ^ 2 + ‖V ξ - ξ‖ ^ 2 := spectralMeasure_energy _ _

end ThomGame.Analysis.CommutingUnitaryPair
