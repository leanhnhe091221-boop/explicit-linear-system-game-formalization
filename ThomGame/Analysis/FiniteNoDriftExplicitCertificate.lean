module

public import ThomGame.Analysis.FiniteNoDriftDouble
public import ThomGame.Analysis.FiniteNoDriftExplicitHeat

/-! The H/N/S weak gaps supply the actual H/Q finite energy certificates. -/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra

variable {d : ℕ} [NeZero d]

theorem finiteNoDrift_explicit_Q_control (f : Compressor.Generator → UnitaryMatrix d)
    {CN CS δ : ℝ} (hCN : 0 ≤ CN) (hCS : 0 ≤ CS)
    (hCNsmall : 60 * CN ≤ (2 : ℝ) ^ 230) (hCSsmall : 144 * CS ≤ (2 : ℝ) ^ 230)
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ (1 / 2 : ℝ) ^ (2 ^ 50000 : ℕ))
    (hf : FiniteNoDriftCompressorModel f δ)
    (hN : FiniteMatrixWeakGap (finiteNoDriftRootTuple f finiteNoDriftCoefficient) (1 / 60) (CN * δ))
    (hS : FiniteMatrixWeakGap (finiteNoDriftShearTuple f) (1 / 144) (CS * δ)) :
    FiniteUCPDefectControl (finiteNoDriftQTuple f)
      (finiteUCPSandwich
        (matrixMarkovPowerCP (finiteNoDriftRootTuple f finiteNoDriftCoefficient) finiteUCPExplicitRootHeatLength)
        (matrixMarkovPowerCP (finiteNoDriftShearTuple f) finiteUCPExplicitShearHeatLength)).toLinearMap
      (1 / 360000) finiteALTExplicitBeta := by
  obtain ⟨hNd, hNe⟩ := finiteNoDrift_explicit_root_heat _ hCN hCNsmall hδ hδsmall hN
  obtain ⟨hSd, hSe⟩ := finiteNoDrift_explicit_shear_heat _ hCS hCSsmall hδ hδsmall hS
  let R := 14 * (4 : ℝ) ^ finiteUCPExplicitShearHeatLength *
    (8 * Real.sqrt 234375 * finiteNoDriftRootHeatEnergy + 3 * δ)
  have hR : ∀ X, matrixOpNorm X ≤ 1 →
      Real.sqrt (matrixCoordinateEnergy (finiteNoDriftRootTuple f finiteNoDriftCoefficient)
        ((matrixLazyMarkov (finiteNoDriftShearTuple f) ^ finiteUCPExplicitShearHeatLength)
          ((matrixLazyMarkov (finiteNoDriftRootTuple f finiteNoDriftCoefficient) ^ finiteUCPExplicitRootHeatLength) X))) ≤ R := by
    intro X hX
    exact finiteNoDrift_root_heat_transport f hf hδ (finiteALT_half_pow_pos _).le _
      ((matrixLazyMarkov_pow_matrixOpNorm_le _ _ X).trans hX) (hNe X hX) _
  have hb := finiteUCP_explicit_sandwich_budget (h := 234375) (by decide)
    (finiteALT_half_pow_pos (2 ^ 40032)).le
    (le_refl finiteNoDriftHeatNoise) (le_refl finiteNoDriftHeatNoise)
    (le_refl finiteNoDriftRootHeatEnergy) (le_refl finiteNoDriftShearHeatEnergy) hδsmall
  refine finiteUCP_heatSandwich_defectControl _ _ _ _ _ (finiteNoDriftQEnergy f)
    hNd hSd hNe hSe hR finiteALT_explicit_beta_pos.le hb.1 ?_
  convert hb.2 using 1 <;> dsimp [R, finiteNoDriftRootHeatEnergy] <;> ring

theorem finiteNoDrift_explicit_energy_certificates (f : Compressor.Generator → UnitaryMatrix d)
    {CH CN CS δ : ℝ} (hCH : 0 ≤ CH) (hCN : 0 ≤ CN) (hCS : 0 ≤ CS)
    (hCHsmall : 60 * CH ≤ (2 : ℝ) ^ 230) (hCNsmall : 60 * CN ≤ (2 : ℝ) ^ 230)
    (hCSsmall : 144 * CS ≤ (2 : ℝ) ^ 230)
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ (1 / 2 : ℝ) ^ (2 ^ 50000 : ℕ))
    (hf : FiniteNoDriftCompressorModel f δ)
    (hH : FiniteMatrixWeakGap (finiteNoDriftRootTuple f finiteNoDriftPositiveCoefficient) (1 / 60) (CH * δ))
    (hN : FiniteMatrixWeakGap (finiteNoDriftRootTuple f finiteNoDriftCoefficient) (1 / 60) (CN * δ))
    (hS : FiniteMatrixWeakGap (finiteNoDriftShearTuple f) (1 / 144) (CS * δ)) :
    ∃ A D : StarSubalgebra ℂ (CMatrix d), FiniteNoDriftEnergyCertificates f A D finiteALTExplicitTolerance := by
  have hHcontrol := finiteNoDrift_explicit_H_control _ hCH hCHsmall hδ hδsmall hH
  have hQcontrol := finiteNoDrift_explicit_Q_control f hCN hCS hCNsmall hCSsmall hδ hδsmall hf hN hS
  obtain ⟨A, hAd, hAe⟩ := exists_finiteUCP_ALT_algebra_explicit _ _
    (matrixLazyMarkov_pow_trace _ _) finiteALT_explicit_H_kappa (by norm_num) hHcontrol le_rfl
  obtain ⟨D, hDd, hDe⟩ := exists_finiteUCP_ALT_algebra_explicit _ _
    (finiteUCPSandwich_trace _ _ (matrixLazyMarkov_pow_trace _ _) (matrixLazyMarkov_pow_trace _ _))
    finiteALT_explicit_Q_kappa (by norm_num) hQcontrol le_rfl
  have h120 : (Real.sqrt (1 / 14400 : ℝ))⁻¹ = 120 := by
    rw [show (1 / 14400 : ℝ) = (1 / 120 : ℝ) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 120)]
    norm_num
  have h600 : (Real.sqrt (1 / 360000 : ℝ))⁻¹ = 600 := by
    rw [show (1 / 360000 : ℝ) = (1 / 600 : ℝ) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 600)]
    norm_num
  refine ⟨A, D, ?_, hAe, ?_, hDe⟩
  · simpa only [h120, show (2 : ℝ) * 120 = 240 by norm_num] using hAd
  · simpa only [h600, show (2 : ℝ) * 600 = 1200 by norm_num] using hDd

end ThomGame.Analysis
