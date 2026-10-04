module

public import ThomGame.Analysis.FiniteNoDriftHeatTransport
public import ThomGame.Analysis.FiniteUCPHeatParameters

/-! Explicit heat estimates, with a uniform dyadic error budget. -/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra

noncomputable def finiteNoDriftHeatNoise : ℝ := (1 / 2 : ℝ) ^ (2 ^ 49997 : ℕ)
noncomputable def finiteNoDriftRootHeatEnergy : ℝ := (1 / 2 : ℝ) ^ (2 ^ 40032 : ℕ)
noncomputable def finiteNoDriftShearHeatEnergy : ℝ := (1 / 2 : ℝ) ^ (2 ^ 40010 : ℕ)

variable {d h : ℕ} [NeZero d] [NeZero h]

theorem finiteNoDrift_explicit_root_heat (U : Fin h → UnitaryMatrix d) {C δ : ℝ}
    (hC : 0 ≤ C) (hCsmall : 60 * C ≤ (2 : ℝ) ^ 230)
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ (1 / 2 : ℝ) ^ (2 ^ 50000 : ℕ))
    (hgap : FiniteMatrixWeakGap U (1 / 60) (C * δ)) :
    (∀ X, matrixOpNorm X ≤ 1 →
      hsNorm (X - (matrixLazyMarkov U ^ finiteUCPExplicitRootHeatLength) X) ≤
        120 * Real.sqrt (matrixCoordinateEnergy U X) + finiteNoDriftHeatNoise) ∧
    (∀ X, matrixOpNorm X ≤ 1 →
      Real.sqrt (matrixCoordinateEnergy U ((matrixLazyMarkov U ^ finiteUCPExplicitRootHeatLength) X)) ≤
        finiteNoDriftRootHeatEnergy) := by
  have hnoise := finiteUCP_explicit_noise_budget hδ hCsmall hδsmall (by decide : 40040 ≤ 40040)
  have henergy := finiteUCP_explicit_root_heat_budget hδ hCsmall hδsmall
  have heq : C * δ / (1 / 60 : ℝ) = (60 * C) * δ := by ring
  constructor
  · intro X hX
    have hh := finiteUCP_weakGap_distance U (by norm_num : (0 : ℝ) < 1 / 60)
      (by norm_num : (1 / 60 : ℝ) ≤ 1) (mul_nonneg hC hδ) hgap finiteUCPExplicitRootHeatLength X hX
    rw [heq] at hh
    norm_num only [show 2 / (1 / 60 : ℝ) = 120 by norm_num] at hh
    exact hh.trans (add_le_add (le_refl _) hnoise)
  · intro X hX
    have hh := finiteUCP_weakGap_uniform_energy_exp U (by norm_num : (0 : ℝ) < 1 / 60)
      (by norm_num : (1 / 60 : ℝ) ≤ 1) (mul_nonneg hC hδ) hgap finiteUCPExplicitRootHeatLength X hX
    rw [heq, show -(finiteUCPExplicitRootHeatLength : ℝ) * (1 / 60) =
      -(finiteUCPExplicitRootHeatLength : ℝ) / 60 by ring] at hh
    exact (Real.sqrt_le_sqrt hh).trans henergy

theorem finiteNoDrift_explicit_shear_heat (U : Fin h → UnitaryMatrix d) {C δ : ℝ}
    (hC : 0 ≤ C) (hCsmall : 144 * C ≤ (2 : ℝ) ^ 230)
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ (1 / 2 : ℝ) ^ (2 ^ 50000 : ℕ))
    (hgap : FiniteMatrixWeakGap U (1 / 144) (C * δ)) :
    (∀ X, matrixOpNorm X ≤ 1 →
      hsNorm (X - (matrixLazyMarkov U ^ finiteUCPExplicitShearHeatLength) X) ≤
        288 * Real.sqrt (matrixCoordinateEnergy U X) + finiteNoDriftHeatNoise) ∧
    (∀ X, matrixOpNorm X ≤ 1 →
      Real.sqrt (matrixCoordinateEnergy U ((matrixLazyMarkov U ^ finiteUCPExplicitShearHeatLength) X)) ≤
        finiteNoDriftShearHeatEnergy) := by
  have hnoise := finiteUCP_explicit_noise_budget hδ hCsmall hδsmall (by decide : 40020 ≤ 40040)
  have henergy := finiteUCP_explicit_shear_heat_budget hδ hCsmall hδsmall
  have heq : C * δ / (1 / 144 : ℝ) = (144 * C) * δ := by ring
  constructor
  · intro X hX
    have hh := finiteUCP_weakGap_distance U (by norm_num : (0 : ℝ) < 1 / 144)
      (by norm_num : (1 / 144 : ℝ) ≤ 1) (mul_nonneg hC hδ) hgap finiteUCPExplicitShearHeatLength X hX
    rw [heq] at hh
    norm_num only [show 2 / (1 / 144 : ℝ) = 288 by norm_num] at hh
    exact hh.trans (add_le_add (le_refl _) hnoise)
  · intro X hX
    have hh := finiteUCP_weakGap_uniform_energy_exp U (by norm_num : (0 : ℝ) < 1 / 144)
      (by norm_num : (1 / 144 : ℝ) ≤ 1) (mul_nonneg hC hδ) hgap finiteUCPExplicitShearHeatLength X hX
    rw [heq, show -(finiteUCPExplicitShearHeatLength : ℝ) * (1 / 144) =
      -(finiteUCPExplicitShearHeatLength : ℝ) / 144 by ring] at hh
    exact (Real.sqrt_le_sqrt hh).trans henergy

theorem finiteNoDrift_explicit_H_control (U : Fin h → UnitaryMatrix d) {C δ : ℝ}
    (hC : 0 ≤ C) (hCsmall : 60 * C ≤ (2 : ℝ) ^ 230)
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ (1 / 2 : ℝ) ^ (2 ^ 50000 : ℕ))
    (hgap : FiniteMatrixWeakGap U (1 / 60) (C * δ)) :
    FiniteUCPDefectControl U (matrixMarkovPowerCP U finiteUCPExplicitRootHeatLength).toLinearMap
      (1 / 14400) finiteALTExplicitBeta := by
  obtain ⟨hd, he⟩ := finiteNoDrift_explicit_root_heat U hC hCsmall hδ hδsmall hgap
  have hnoise : finiteNoDriftHeatNoise ≤ finiteALTExplicitBeta :=
    finiteUCP_dyadic_double_antitone (by decide : 40000 ≤ 49997)
  have henergy : finiteNoDriftRootHeatEnergy ≤ finiteALTExplicitBeta :=
    finiteUCP_dyadic_double_antitone (by decide : 40000 ≤ 40032)
  have hs : (Real.sqrt (1 / 14400 : ℝ))⁻¹ = 120 := by
    rw [show (1 / 14400 : ℝ) = (1 / 120 : ℝ) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 120)]
    norm_num
  rw [matrixMarkovPowerCP_toLinearMap]
  refine ⟨finiteALT_explicit_beta_pos.le, ?_, ?_⟩
  · intro X hX
    rw [hs]
    exact (hd X hX).trans (add_le_add (le_refl _) hnoise)
  · intro X hX
    exact (he X hX).trans henergy

end ThomGame.Analysis
