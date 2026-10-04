module

public import ThomGame.Analysis.CommutingUnitarySpectralMeasure
public import ThomGame.Analysis.HilbertVectorMeasureAtoms

/-! A vector orthogonal to the common fixed space has zero spectral mass at the torus origin. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open IntegerTorus MeasureTheory

def torusEnergyFunction : C(Torus, ℝ) := ⟨coordinateEnergy, coordinateEnergy_continuous⟩

def torusOriginCutoff : C(Torus, ℂ) :=
  1 - (1 / 8 : ℂ) • continuousComplexify torusEnergyFunction

theorem torusOriginCutoff_zero : torusOriginCutoff (0 : Torus) = 1 := by
  norm_num [torusOriginCutoff, torusEnergyFunction, continuousComplexify, coordinateEnergy]

theorem torusOriginCutoff_norm_le : ‖torusOriginCutoff‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ zero_le_one).mpr
  intro x
  have hn := coordinateEnergy_nonneg x
  have hb := coordinateEnergy_le_eight x
  have h₀ : 0 ≤ 1 - (1 / 8 : ℝ) * coordinateEnergy x := by linarith
  have h₁ : 1 - (1 / 8 : ℝ) * coordinateEnergy x ≤ 1 := by linarith
  change ‖(1 : ℂ) - (1 / 8 : ℂ) * (coordinateEnergy x : ℂ)‖ ≤ 1
  have hc : (1 : ℂ) - (1 / 8 : ℂ) * (coordinateEnergy x : ℂ) =
      ((1 - (1 / 8 : ℝ) * coordinateEnergy x : ℝ) : ℂ) := by push_cast; rfl
  rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h₀]
  exact h₁

namespace CommutingUnitaryPair

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def commonFixed (p : CommutingUnitaryPair (H →L[ℂ] H)) : Submodule ℂ H :=
  (p.first : H →L[ℂ] H).eqLocus 1 ⊓ (p.second : H →L[ℂ] H).eqLocus 1

theorem torusOriginCutoff_calculus_norm_le (p : CommutingUnitaryPair (H →L[ℂ] H)) :
    ‖p.calculus torusOriginCutoff‖ ≤ 1 :=
  (calculus_norm_le p torusOriginCutoff).trans torusOriginCutoff_norm_le

theorem torusOriginCutoff_fixed_common (p : CommutingUnitaryPair (H →L[ℂ] H)) (η : H)
    (hη : p.calculus torusOriginCutoff η = η) : η ∈ commonFixed p := by
  have hz : p.calculus (continuousComplexify torusEnergyFunction) η = 0 := by
    have h : η - (1 / 8 : ℂ) • p.calculus (continuousComplexify torusEnergyFunction) η = η := by
      simpa only [torusOriginCutoff, map_sub, map_one, map_smul, sub_apply,
        one_apply_eq_self, smul_apply] using hη
    have hs : (1 / 8 : ℂ) • p.calculus (continuousComplexify torusEnergyFunction) η = 0 :=
      sub_eq_self.mp h
    exact (smul_eq_zero.mp hs).resolve_left (by norm_num)
  have hi : (∫ z, coordinateEnergy z ∂spectralMeasure p η) = 0 := by
    change (∫ z, torusEnergyFunction z ∂hilbertVectorMeasure p.calculus η) = 0
    rw [hilbertVectorMeasure_integral, hilbertContinuousVectorState_apply, hz,
      inner_zero_right, Complex.zero_re]
  rw [spectralMeasure_energy] at hi
  have h₁ : ‖(p.first : H →L[ℂ] H) η - η‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖(p.second : H →L[ℂ] H) η - η‖]
  have h₂ : ‖(p.second : H →L[ℂ] H) η - η‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖(p.first : H →L[ℂ] H) η - η‖]
  exact ⟨sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp h₁)),
    sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp h₂))⟩

theorem spectralMeasure_origin_null (p : CommutingUnitaryPair (H →L[ℂ] H)) (ξ : H)
    (hξ : ξ ∈ (commonFixed p)ᗮ) : (spectralMeasure p ξ).real {(0 : Torus)} = 0 := by
  apply hilbertVectorMeasure_atom_zero_of_orthogonal p.calculus ξ torusOriginCutoff 0
    torusOriginCutoff_zero (torusOriginCutoff_calculus_norm_le p)
  apply (Submodule.mem_orthogonal _ _).mpr
  intro η hη
  exact (Submodule.mem_orthogonal _ _).mp hξ η (torusOriginCutoff_fixed_common p η hη)

end CommutingUnitaryPair
end ThomGame.Analysis
