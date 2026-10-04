module

public import ThomGame.Analysis.IntegralShearKazhdan
public import ThomGame.Analysis.CompressorShearKazhdanGap

/-! Unconditional property (T) and a specified-generator gap for the actual compressor Q. -/

@[expose] public noncomputable section
namespace ThomGame.Compressor

universe u

open Analysis

theorem hasFiniteHilbertKazhdanSet : HasFiniteHilbertKazhdanSet.{u} GroupQ :=
  hasFiniteHilbertKazhdanSet_of_shear integralShear_hasFiniteHilbertKazhdanSet

def generatorKazhdanConstant : ℝ :=
  shearGeneratorKazhdanConstant integralShearKazhdanSet integralShearKazhdanConstant

theorem generatorKazhdanConstant_pos : 0 < generatorKazhdanConstant :=
  shearGeneratorKazhdanConstant_pos _ integralShearKazhdanConstant_pos

theorem generatorTuple_displacement
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : GroupQ →* (H ≃ₗᵢ[ℂ] H)) (x : H) (hx : x ∈ (hilbertUnitaryInvariants ρ)ᗮ) :
    ∃ j : Fin 48, generatorKazhdanConstant * ‖x‖ ≤ ‖ρ (generatorTuple j) x - x‖ :=
  generatorTuple_displacement_of_shear integralShearKazhdanSet integralShearKazhdanConstant
    integralShearKazhdanConstant_pos integralShear_hilbertKazhdanBound ρ x hx

theorem generatorTuple_energy
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : GroupQ →* (H ≃ₗᵢ[ℂ] H)) (x : H) (hx : x ∈ (hilbertUnitaryInvariants ρ)ᗮ) :
    generatorKazhdanConstant ^ 2 * ‖x‖ ^ 2 ≤ ∑ j : Fin 48, ‖ρ (generatorTuple j) x - x‖ ^ 2 :=
  generatorTuple_energy_of_shear integralShearKazhdanSet integralShearKazhdanConstant
    integralShearKazhdanConstant_pos integralShear_hilbertKazhdanBound ρ x hx

end ThomGame.Compressor
