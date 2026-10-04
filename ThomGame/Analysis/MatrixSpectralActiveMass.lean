module

public import ThomGame.Analysis.MatrixSpectralCut
public import ThomGame.Analysis.SpectralRestrictedCoarea

/-!
# The mass of active spectral pairs

Row and column masses of the actual matrix energy weights bound the
active mass by half the normalized trace of a spectral cut, and hence
by the normalized trace of a positive matrix divided by `2a`.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

variable {d h : Nat} [NeZero h]

theorem matrixEnergyWeight_step_sum (U : Fin h → UnitaryMatrix d) (e : Fin d → ℝ) (a : ℝ) :
    (∑ i, ∑ j, matrixEnergyWeight U i j * (spectralStep a (e i) + spectralStep a (e j))) =
      (∑ i, spectralStep a (e i)) / (2 * d) := by
  have hr : (∑ i, ∑ j, matrixEnergyWeight U i j * spectralStep a (e i)) =
      (4 * (d : ℝ))⁻¹ * ∑ i, spectralStep a (e i) := by
    simp only [← Finset.sum_mul, matrixEnergyWeight_row_sum, ← Finset.mul_sum]
  have hc : (∑ i, ∑ j, matrixEnergyWeight U i j * spectralStep a (e j)) =
      (4 * (d : ℝ))⁻¹ * ∑ i, spectralStep a (e i) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, matrixEnergyWeight_col_sum, ← Finset.mul_sum]
  simp only [mul_add, Finset.sum_add_distrib, hr, hc, div_eq_mul_inv, mul_inv_rev]
  ring

theorem matrixEnergyWeight_active_mass_le (U : Fin h → UnitaryMatrix d)
    (e : Fin d → ℝ) (a : ℝ) :
    (∑ i, ∑ j, spectralActiveWeight a (matrixEnergyWeight U i j) (e i) (e j)) ≤
      (∑ i, spectralStep a (e i)) / (2 * d) := by
  rw [← matrixEnergyWeight_step_sum U e a]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    spectralActiveWeight_le_steps a _ _ _ (matrixEnergyWeight_nonneg U i j)

theorem matrixEnergyWeight_active_mass_trace_le (U : Fin h → UnitaryMatrix d)
    (e : Fin d → ℝ) (he : ∀ i, 0 ≤ e i) (a : ℝ) (ha : 0 < a) :
    (∑ i, ∑ j, spectralActiveWeight a (matrixEnergyWeight U i j) (e i) (e j)) ≤
      ((∑ i, e i) / d) / (2 * a) := by
  have hs : a * (∑ i, spectralStep a (e i)) ≤ ∑ i, e i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => spectralStep_mul_le a _ (he i)
  have hs' : (∑ i, spectralStep a (e i)) ≤ (∑ i, e i) / a := by
    exact (le_div_iff₀ ha).2 (by simpa only [mul_comm] using hs)
  calc
    _ ≤ (∑ i, spectralStep a (e i)) / (2 * d) := matrixEnergyWeight_active_mass_le U e a
    _ ≤ ((∑ i, e i) / a) / (2 * d) := div_le_div_of_nonneg_right hs' (by positivity)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

theorem matrixSpectralActiveMass_le {X : CMatrix d} (hX : X.PosSemidef)
    (U : Fin h → UnitaryMatrix d) (a : ℝ) (ha : 0 < a) :
    (∑ i, ∑ j, spectralActiveWeight a (matrixEnergyWeight (matrixEigenbasisTuple hX.isHermitian U) i j)
      (hX.isHermitian.eigenvalues i) (hX.isHermitian.eigenvalues j)) ≤
      (normalizedTrace X).re / (2 * a) := by
  rw [normalizedTrace_eq_eigenvalue_sum hX.isHermitian]
  exact matrixEnergyWeight_active_mass_trace_le _ _ hX.eigenvalues_nonneg a ha

end ThomGame.Analysis
