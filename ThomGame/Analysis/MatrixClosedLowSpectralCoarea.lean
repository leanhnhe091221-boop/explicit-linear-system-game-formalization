module

public import ThomGame.Analysis.MatrixClosedLowSpectralCut
public import ThomGame.Analysis.MatrixSpectralCoarea
public import ThomGame.Analysis.MatrixPolarDilation

/-!
# Coarea for actual closed low spectral intervals

Apply upper-cut coarea to the negative matrix to retain the closed
endpoint exactly. Composing the actual square root transports the
threshold back to the original positive matrix.
-/

@[expose] public section
namespace ThomGame.Analysis

open Set
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d h : Nat}

theorem matrixCoordinateEnergy_neg (U : Fin h → UnitaryMatrix d) (X : CMatrix d) :
    matrixCoordinateEnergy U (-X) = matrixCoordinateEnergy U X := by
  have he (j : Fin h) : (U j).val * (-X) - (-X) * (U j).val =
      -((U j).val * X - X * (U j).val) := by
    rw [Matrix.mul_neg, Matrix.neg_mul]
    abel
  simp only [matrixCoordinateEnergy, he, hsNorm_neg]

theorem matrixClosedLowSpectralCut_eq_negative_cut {X : CMatrix d} (hX : 0 ≤ X) (s : ℝ) :
    matrixClosedLowSpectralCut X s = matrixSpectralCut (-X) (-s) := by
  rw [matrixClosedLowSpectralCut, matrixSpectralCut,
    ← cfc_comp_neg (spectralStep (-s)) X
      ((X.finite_real_spectrum.image (fun t : ℝ => -t)).continuousOn _) hX.isSelfAdjoint]
  apply cfc_congr
  intro t ht
  simp only [spectralStep, neg_le_neg_iff, spectrum_nonneg_of_nonneg hX ht, true_and]

theorem matrixClosedLowSpectralCut_sqrt {X : CMatrix d} (hX : 0 ≤ X) {s : ℝ} (hs : 0 ≤ s) :
    matrixClosedLowSpectralCut (CFC.sqrt X) s = matrixClosedLowSpectralCut X (s ^ 2) := by
  rw [matrixClosedLowSpectralCut, matrixSqrt_eq_real_cfc hX,
    ← cfc_comp' (fun t : ℝ => if 0 ≤ t ∧ t ≤ s then 1 else 0) Real.sqrt X
      ((X.finite_real_spectrum.image Real.sqrt).continuousOn _)
      (X.finite_real_spectrum.continuousOn _) hX.isSelfAdjoint, matrixClosedLowSpectralCut]
  apply cfc_congr
  intro t ht
  simp only [Real.sqrt_nonneg, spectrum_nonneg_of_nonneg hX ht, true_and,
    Real.sqrt_le_iff, hs]

theorem exists_matrixClosedLowSpectralCut_energy_le [NeZero d] [NeZero h]
    (U : Fin h → UnitaryMatrix d) {X : CMatrix d} (hX : 0 ≤ X) {a b : ℝ} (hab : a < b) :
    ∃ s ∈ Icc a b, matrixCoordinateEnergy U (matrixClosedLowSpectralCut X s) ≤
      Real.sqrt (matrixCoordinateEnergy U X) / (2 * (b - a)) := by
  obtain ⟨t, ht, he⟩ := exists_matrixSpectralCut_energy_le hX.isSelfAdjoint.isHermitian.neg U
    (-b) (-a) (neg_lt_neg hab)
  refine ⟨-t, ⟨by linarith only [ht.2], by linarith only [ht.1]⟩, ?_⟩
  rw [matrixClosedLowSpectralCut_eq_negative_cut hX, neg_neg]
  simpa only [matrixCoordinateEnergy_neg, neg_sub_neg] using he

theorem exists_matrixClosedLowSpectralCut_sqrt_energy_le [NeZero d] [NeZero h]
    (U : Fin h → UnitaryMatrix d) {X : CMatrix d} (hX : 0 ≤ X)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∃ s ∈ Icc (a ^ 2) (b ^ 2), matrixCoordinateEnergy U (matrixClosedLowSpectralCut X s) ≤
      Real.sqrt (matrixCoordinateEnergy U (CFC.sqrt X)) / (2 * (b - a)) := by
  obtain ⟨t, ht, he⟩ := exists_matrixClosedLowSpectralCut_energy_le U (CFC.sqrt_nonneg X) hab
  have ht0 : 0 ≤ t := ha.trans ht.1
  refine ⟨t ^ 2, ⟨?_, ?_⟩, ?_⟩
  · exact (sq_le_sq₀ ha ht0).mpr ht.1
  · exact (sq_le_sq₀ ht0 (ha.trans hab.le)).mpr ht.2
  · rwa [matrixClosedLowSpectralCut_sqrt hX ht0] at he

end ThomGame.Analysis
