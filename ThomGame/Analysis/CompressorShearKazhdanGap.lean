module

public import ThomGame.Analysis.HilbertKazhdanExtension
public import ThomGame.Analysis.HilbertKazhdanGeneratingTuple
public import ThomGame.Analysis.CompressorFiniteKazhdanSets
public import ThomGame.Groups.CompressorShearQuotient
public import ThomGame.Groups.CompressorGeneratingTuples

/-!
# Q's finite Kazhdan and generator bounds from the actual shear group

N's bound is proved. The only hypothesis here is a finite Hilbert
Kazhdan bound for the six-generator integral shear presentation.
-/

@[expose] public noncomputable section
namespace ThomGame.Compressor

universe u

open Analysis

theorem elementaryHilbertKazhdanBound :
    HilbertKazhdanBound.{u} elementaryKazhdanSet primeFiveKazhdanConstant := by
  intro H _ _ _ ρ x hx
  exact elementaryKazhdanSet_displacement ρ x hx

def shearExtensionKazhdanSet (S : Finset IntegralShear.ShearGroup) : Finset GroupQ :=
  normalExtensionKazhdanSet elementarySubgroup integralShearToQ elementaryKazhdanSet S

def shearExtensionKazhdanConstant (b : ℝ) : ℝ :=
  normalExtensionKazhdanConstant primeFiveKazhdanConstant b

theorem shearExtensionKazhdanConstant_pos {b : ℝ} (hb : 0 < b) :
    0 < shearExtensionKazhdanConstant b :=
  normalExtensionKazhdanConstant_pos primeFiveKazhdanConstant_pos hb

theorem hilbertKazhdanBound_of_shear (S : Finset IntegralShear.ShearGroup) (b : ℝ) (hb : 0 < b)
    (hS : HilbertKazhdanBound.{u} S b) :
    HilbertKazhdanBound.{u} (shearExtensionKazhdanSet S) (shearExtensionKazhdanConstant b) :=
  hilbertKazhdanBound_normalExtension elementarySubgroup integralShearToQ
    integralShearToQuotient_surjective elementaryKazhdanSet S primeFiveKazhdanConstant b
    primeFiveKazhdanConstant_pos hb elementaryHilbertKazhdanBound hS

theorem hasFiniteHilbertKazhdanSet_of_shear
    (hShear : HasFiniteHilbertKazhdanSet.{u} IntegralShear.ShearGroup) :
    HasFiniteHilbertKazhdanSet.{u} GroupQ := by
  obtain ⟨S, b, hb, hS⟩ := hShear
  exact ⟨shearExtensionKazhdanSet S, shearExtensionKazhdanConstant b,
    shearExtensionKazhdanConstant_pos hb, hilbertKazhdanBound_of_shear S b hb hS⟩

def shearGeneratorWordConstant (S : Finset IntegralShear.ShearGroup) : Nat :=
  generatingTupleWordConstant generatorTuple generatorTuple_generates (shearExtensionKazhdanSet S)

theorem shearGeneratorWordConstant_pos (S : Finset IntegralShear.ShearGroup) :
    0 < shearGeneratorWordConstant S := generatingTupleWordConstant_pos _ _ _

def shearGeneratorKazhdanConstant (S : Finset IntegralShear.ShearGroup) (b : ℝ) : ℝ :=
  generatingTupleKazhdanConstant generatorTuple generatorTuple_generates
    (shearExtensionKazhdanSet S) (shearExtensionKazhdanConstant b)

theorem shearGeneratorKazhdanConstant_formula (S : Finset IntegralShear.ShearGroup) (b : ℝ) :
    shearGeneratorKazhdanConstant S b =
      (min primeFiveKazhdanConstant b / 2) / shearGeneratorWordConstant S := rfl

theorem shearGeneratorKazhdanConstant_pos (S : Finset IntegralShear.ShearGroup) {b : ℝ} (hb : 0 < b) :
    0 < shearGeneratorKazhdanConstant S b :=
  generatingTupleKazhdanConstant_pos _ _ _ (shearExtensionKazhdanConstant_pos hb)

theorem generatorTuple_displacement_of_shear (S : Finset IntegralShear.ShearGroup) (b : ℝ) (hb : 0 < b)
    (hS : HilbertKazhdanBound.{u} S b)
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : GroupQ →* (H ≃ₗᵢ[ℂ] H)) (x : H) (hx : x ∈ (hilbertUnitaryInvariants ρ)ᗮ) :
    ∃ j : Fin 48, shearGeneratorKazhdanConstant S b * ‖x‖ ≤ ‖ρ (generatorTuple j) x - x‖ :=
  generatingTuple_displacement_of_kazhdanBound generatorTuple generatorTuple_generates
    (shearExtensionKazhdanSet S) (shearExtensionKazhdanConstant b)
    (hilbertKazhdanBound_of_shear S b hb hS) ρ x hx

theorem generatorTuple_energy_of_shear (S : Finset IntegralShear.ShearGroup) (b : ℝ) (hb : 0 < b)
    (hS : HilbertKazhdanBound.{u} S b)
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : GroupQ →* (H ≃ₗᵢ[ℂ] H)) (x : H) (hx : x ∈ (hilbertUnitaryInvariants ρ)ᗮ) :
    shearGeneratorKazhdanConstant S b ^ 2 * ‖x‖ ^ 2 ≤ ∑ j : Fin 48, ‖ρ (generatorTuple j) x - x‖ ^ 2 :=
  generatingTuple_energy_of_kazhdanBound generatorTuple generatorTuple_generates
    (shearExtensionKazhdanSet S) (shearExtensionKazhdanConstant b)
    (shearExtensionKazhdanConstant_pos hb) (hilbertKazhdanBound_of_shear S b hb hS) ρ x hx

theorem exists_generatorTuple_energy_gap_of_shear
    (hShear : HasFiniteHilbertKazhdanSet.{u} IntegralShear.ShearGroup) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
        ∀ (ρ : GroupQ →* (H ≃ₗᵢ[ℂ] H)) (x : H), x ∈ (hilbertUnitaryInvariants ρ)ᗮ →
          c * ‖x‖ ^ 2 ≤ ∑ j : Fin 48, ‖ρ (generatorTuple j) x - x‖ ^ 2 :=
  exists_generatingTuple_energy_gap generatorTuple generatorTuple_generates
    (hasFiniteHilbertKazhdanSet_of_shear hShear)

end ThomGame.Compressor
