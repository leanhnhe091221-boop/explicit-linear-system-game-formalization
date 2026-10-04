module

public import ThomGame.Analysis.MatrixSpectralCut

/-!
# Spectral coarea for a self-adjoint matrix

The actual spectral cuts obey ALT Lemma 2.3, first inequality, with
constant one half. The threshold is selected from the given interval
using the first moment method, which needs no continuity of the cuts.
-/

@[expose] public section
namespace ThomGame.Analysis

open MeasureTheory Set
open scoped BigOperators Matrix.Norms.L2Operator

variable {d h : Nat} {X : CMatrix d}

theorem matrixSpectralCut_energy_intervalIntegrable (hX : Matrix.IsHermitian X)
    (U : Fin h → UnitaryMatrix d) (a b : ℝ) :
    IntervalIntegrable (fun s => matrixCoordinateEnergy U (matrixSpectralCut X s)) volume a b := by
  have he : (fun s => matrixCoordinateEnergy U (matrixSpectralCut X s)) =
      (fun s => ∑ p : Fin d × Fin d, matrixEnergyWeight (matrixEigenbasisTuple hX U) p.1 p.2 *
        (spectralStep s (hX.eigenvalues p.2) - spectralStep s (hX.eigenvalues p.1)) ^ 2) := by
    funext s
    rw [matrixSpectralCut_energy hX, Fintype.sum_prod_type]
  rw [he]
  exact weighted_spectralStep_intervalIntegrable a b _ _ _

variable [NeZero d] [NeZero h]

theorem matrixSpectralCut_coarea (hX : Matrix.IsHermitian X)
    (U : Fin h → UnitaryMatrix d) (a b : ℝ) (hab : a ≤ b) :
    (∫ s in a..b, matrixCoordinateEnergy U (matrixSpectralCut X s)) ≤
      (1 / 2 : ℝ) * Real.sqrt (matrixCoordinateEnergy U X) := by
  have he := weighted_spectralStep_coarea a b hab
    (fun p : Fin d × Fin d => matrixEnergyWeight (matrixEigenbasisTuple hX U) p.1 p.2)
    (fun p => hX.eigenvalues p.1) (fun p => hX.eigenvalues p.2)
    (fun p => matrixEnergyWeight_nonneg _ p.1 p.2)
  simp only [Fintype.sum_prod_type, ← matrixSpectralCut_energy hX,
    matrixEnergyWeight_total, ← matrixCoordinateEnergy_spectral hX] at he
  calc
    _ ≤ _ := he
    _ = _ := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1 / 4),
        show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]

theorem exists_matrixSpectralCut_energy_le (hX : Matrix.IsHermitian X)
    (U : Fin h → UnitaryMatrix d) (a b : ℝ) (hab : a < b) :
    ∃ s ∈ Icc a b, matrixCoordinateEnergy U (matrixSpectralCut X s) ≤
      Real.sqrt (matrixCoordinateEnergy U X) / (2 * (b - a)) := by
  obtain ⟨s, hs, hse⟩ := exists_le_intervalIntegral_average hab
    (matrixSpectralCut_energy_intervalIntegrable hX U a b)
  refine ⟨s, hs, hse.trans ?_⟩
  calc
    _ ≤ ((1 / 2 : ℝ) * Real.sqrt (matrixCoordinateEnergy U X)) / (b - a) :=
      div_le_div_of_nonneg_right (matrixSpectralCut_coarea hX U a b hab.le) (sub_nonneg.mpr hab.le)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

end ThomGame.Analysis
