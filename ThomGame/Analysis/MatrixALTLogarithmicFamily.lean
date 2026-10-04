module

public import ThomGame.Analysis.ALTLogarithmicParameters

/-!
# The positive-energy case of ALT Proposition 3.5

The partial isometries are the actual matrix family constructed for
(3.14). The estimates below record explicit absolute constants.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {μ : Type*} [Fintype μ] [DecidableEq μ] {d h : Nat} [NeZero d] [NeZero h]

theorem exists_matrixOrthogonalFamily_exponential {q : μ → CMatrix d}
    (hq : ∀ i, IsStarProjection (q i)) (U : Fin h → UnitaryMatrix d)
    {t : ℝ} (htrace : ∑ i, matrixTraceReal d (q i) ≤ 3)
    (henergy : ∑ i, matrixCoordinateEnergy U (q i) ≤ Real.exp (-16 * t)) (ht : 1 ≤ t) :
    ∃ V : μ → CMatrix d,
      (∀ i, IsStarProjection ((V i)ᴴ * V i)) ∧
      (∀ i, IsStarProjection (V i * (V i)ᴴ)) ∧
      (∀ i, V i * (V i)ᴴ ≤ q i) ∧
      Pairwise (fun i j => ((V i)ᴴ * V i) * ((V j)ᴴ * V j) = 0) ∧
      (∑ i, matrixCoordinateEnergy U (V i)) ≤ 74 * (Real.sqrt t)⁻¹ ∧
      (∑ i, matrixCoordinateEnergy U ((V i)ᴴ * V i)) ≤ 296 * (Real.sqrt t)⁻¹ ∧
      matrixFamilyCoverageDefect (fun i => (V i)ᴴ * V i) - matrixFamilyCoverageDefect q ≤
        4 * (Real.sqrt t)⁻¹ := by
  obtain ⟨V, hVi, hVf, hVq, horth, he, hpe, hcov⟩ :=
    exists_matrixOrthogonalFamily_ALT_3_14 hq U htrace henergy (Real.exp_pos (-2 * t)) ht
  have hb := he.trans (alt_exponential_energy_bound ht)
  refine ⟨V, hVi, hVf, hVq, horth, hb, ?_, ?_⟩
  · linarith
  · exact hcov.trans (mul_le_mul_of_nonneg_left (alt_exp_neg_two_le_inv_sqrt ht) (by norm_num))

theorem exists_matrixOrthogonalFamily_ALT_proposition3_5_pos {q : μ → CMatrix d}
    (hq : ∀ i, IsStarProjection (q i)) (U : Fin h → UnitaryMatrix d)
    {s : ℝ} (htrace : ∑ i, matrixTraceReal d (q i) ≤ 3)
    (henergy : ∑ i, matrixCoordinateEnergy U (q i) ≤ s)
    (hs : 0 < s) (hsmall : s ≤ Real.exp (-16)) :
    ∃ V : μ → CMatrix d,
      (∀ i, IsStarProjection ((V i)ᴴ * V i)) ∧
      (∀ i, IsStarProjection (V i * (V i)ᴴ)) ∧
      (∀ i, V i * (V i)ᴴ ≤ q i) ∧
      Pairwise (fun i j => ((V i)ᴴ * V i) * ((V j)ᴴ * V j) = 0) ∧
      (∑ i, matrixCoordinateEnergy U (V i)) ≤ 296 * (Real.sqrt (Real.log (1 / s)))⁻¹ ∧
      (∑ i, matrixCoordinateEnergy U ((V i)ᴴ * V i)) ≤ 1184 * (Real.sqrt (Real.log (1 / s)))⁻¹ ∧
      matrixFamilyCoverageDefect (fun i => (V i)ᴴ * V i) - matrixFamilyCoverageDefect q ≤
        16 * (Real.sqrt (Real.log (1 / s)))⁻¹ := by
  obtain ⟨ht, heq, hscale⟩ := alt_logarithmic_parameters hs hsmall
  obtain ⟨V, hVi, hVf, hVq, horth, he, hpe, hcov⟩ :=
    exists_matrixOrthogonalFamily_exponential hq U htrace (heq.symm ▸ henergy) ht
  rw [hscale] at he hpe hcov
  refine ⟨V, hVi, hVf, hVq, horth, ?_, ?_, ?_⟩ <;> linarith

end ThomGame.Analysis
