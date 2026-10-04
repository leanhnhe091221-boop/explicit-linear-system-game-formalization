module

public import ThomGame.Analysis.IntegerLatticeSpectralMeasure
public import ThomGame.Analysis.IntegerTorusCalculusUniqueness
public import ThomGame.Analysis.IntegerTorusShearMeasureControl

/-! Genuine shear covariance of the integer-lattice functional calculus. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open IntegerTorus

theorem coordinateCharacter_shear (b c : Bool) :
    (coordinateCharacter c).comp ⟨integerShear b 1, (integerShear b 1).continuous⟩ =
      if b = c then coordinateCharacter c else coordinateCharacter false * coordinateCharacter true := by
  cases b <;> cases c <;> ext x <;>
    simp [coordinateCharacter, integerShear, lower, upper, character_add, mul_comm]

theorem lattice_shear_generator (b c : Bool) :
    IntegerPlane.shear b (latticeGenerator c) =
      if b = c then latticeGenerator c else latticeGenerator false * latticeGenerator true := by
  cases b <;> cases c <;> rfl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem latticeCalculus_coordinate (ρ : IntegerPlane.Group →* (H ≃ₗᵢ[ℂ] H)) (b : Bool) :
    (latticeUnitaryPair ρ).calculus (coordinateCharacter b) =
      (ρ (latticeGenerator b) : H →L[ℂ] H) := by
  cases b
  · rw [CommutingUnitaryPair.calculus_first]
    rfl
  · rw [CommutingUnitaryPair.calculus_second]
    rfl

theorem latticeCalculus_sheared_coordinate (ρ : IntegerPlane.Group →* (H ≃ₗᵢ[ℂ] H)) (b c : Bool) :
    (latticeUnitaryPair ρ).calculus
      ((coordinateCharacter c).comp ⟨integerShear b 1, (integerShear b 1).continuous⟩) =
      (ρ (IntegerPlane.shear b (latticeGenerator c)) : H →L[ℂ] H) := by
  rw [coordinateCharacter_shear, lattice_shear_generator]
  by_cases h : b = c
  · simp only [h, ↓reduceIte, latticeCalculus_coordinate]
  · simp only [h, ↓reduceIte, map_mul, latticeCalculus_coordinate]
    rfl

theorem latticeCalculus_shear_covariant (ρ : IntegerPlane.Group →* (H ≃ₗᵢ[ℂ] H))
    (S : H ≃ₗᵢ[ℂ] H) (b : Bool)
    (hS : ∀ v : IntegerPlane.Group, S * ρ v * S⁻¹ = ρ (IntegerPlane.shear b v))
    (f : C(Torus, ℂ)) :
    (latticeUnitaryPair ρ).calculus (f.comp ⟨integerShear b 1, (integerShear b 1).continuous⟩) =
      S.conjStarAlgEquiv ((latticeUnitaryPair ρ).calculus f) := by
  let e : C(Torus, Torus) := ⟨integerShear b 1, (integerShear b 1).continuous⟩
  have heq : (latticeUnitaryPair ρ).calculus.comp (e.compStarAlgHom' ℂ ℂ) =
      S.conjStarAlgEquiv.toStarAlgHom.comp (latticeUnitaryPair ρ).calculus := by
    apply torusStarAlgHom_ext
    intro c
    change (latticeUnitaryPair ρ).calculus ((coordinateCharacter c).comp e) =
      S.conjStarAlgEquiv ((latticeUnitaryPair ρ).calculus (coordinateCharacter c))
    rw [latticeCalculus_sheared_coordinate, latticeCalculus_coordinate]
    apply ContinuousLinearMap.ext
    intro x
    exact congrArg (fun W : H ≃ₗᵢ[ℂ] H => W x) (hS (latticeGenerator c)).symm
  exact congrArg (fun φ : C(Torus, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) => φ f) heq

end ThomGame.Analysis
