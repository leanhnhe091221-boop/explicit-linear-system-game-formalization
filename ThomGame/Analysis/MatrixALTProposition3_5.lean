module

public import ThomGame.Analysis.MatrixALTZeroEnergyFamily

/-!
# ALT Proposition 3.5 with an explicit absolute constant

This includes zero energy. At `s = 0`, Lean's totalized scalar
operations make the right side zero; the conclusion is furnished by
the exact compactness argument, not by substituting into an estimate
that requires positive energy.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {μ : Type*} [Fintype μ] [DecidableEq μ] {d h : Nat} [NeZero d] [NeZero h]

theorem exists_matrixOrthogonalFamily_ALT_proposition3_5 {q : μ → CMatrix d}
    (hq : ∀ i, IsStarProjection (q i)) (U : Fin h → UnitaryMatrix d)
    {s : ℝ} (htrace : ∑ i, matrixTraceReal d (q i) ≤ 3)
    (henergy : ∑ i, matrixCoordinateEnergy U (q i) ≤ s) (hsmall : s ≤ Real.exp (-16)) :
    ∃ V : μ → CMatrix d,
      (∀ i, IsStarProjection ((V i)ᴴ * V i)) ∧
      (∀ i, IsStarProjection (V i * (V i)ᴴ)) ∧
      (∀ i, V i * (V i)ᴴ ≤ q i) ∧
      Pairwise (fun i j => ((V i)ᴴ * V i) * ((V j)ᴴ * V j) = 0) ∧
      (∑ i, matrixCoordinateEnergy U (V i)) ≤ 1184 * (Real.sqrt (Real.log (1 / s)))⁻¹ ∧
      (∑ i, matrixCoordinateEnergy U ((V i)ᴴ * V i)) ≤ 1184 * (Real.sqrt (Real.log (1 / s)))⁻¹ ∧
      matrixFamilyCoverageDefect (fun i => (V i)ᴴ * V i) - matrixFamilyCoverageDefect q ≤
        1184 * (Real.sqrt (Real.log (1 / s)))⁻¹ := by
  by_cases hs : s = 0
  · subst s
    obtain ⟨V, hVi, hVf, hVq, horth, he, hpe, hcov⟩ :=
      exists_matrixOrthogonalFamily_ALT_proposition3_5_zero hq U htrace henergy
    refine ⟨V, hVi, hVf, hVq, horth, ?_, ?_, ?_⟩
    · simp only [div_zero, Real.log_zero, Real.sqrt_zero, _root_.inv_zero, mul_zero, he, le_refl]
    · simp only [div_zero, Real.log_zero, Real.sqrt_zero, _root_.inv_zero, mul_zero, hpe, le_refl]
    · simpa only [div_zero, Real.log_zero, Real.sqrt_zero, _root_.inv_zero, mul_zero, sub_nonpos] using hcov
  · have hs0 : 0 ≤ s :=
      (Finset.sum_nonneg fun i _ => matrixCoordinateEnergy_nonneg U (q i)).trans henergy
    obtain ⟨V, hVi, hVf, hVq, horth, he, hpe, hcov⟩ :=
      exists_matrixOrthogonalFamily_ALT_proposition3_5_pos hq U htrace henergy (lt_of_le_of_ne hs0 (Ne.symm hs)) hsmall
    have hp : 0 ≤ (Real.sqrt (Real.log (1 / s)))⁻¹ := by positivity
    refine ⟨V, hVi, hVf, hVq, horth, ?_, hpe, ?_⟩ <;> linarith

end ThomGame.Analysis
