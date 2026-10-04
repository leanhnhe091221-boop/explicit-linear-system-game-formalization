module

public import ThomGame.Analysis.MatrixOrthogonalFamilyCompactness

/-!
# The exact zero-energy case of ALT Proposition 3.5

Minimize a continuous nonnegative defect on the compact space of
actual matrix families. The exponential construction makes its minimum
arbitrarily small. The minimizer therefore has exactly zero energy
and no additional coverage defect.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix Filter
open scoped BigOperators Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {μ : Type*} [Fintype μ] [DecidableEq μ] {d h : Nat} [NeZero d] [NeZero h]

theorem exists_matrixOrthogonalFamily_ALT_proposition3_5_zero {q : μ → CMatrix d}
    (hq : ∀ i, IsStarProjection (q i)) (U : Fin h → UnitaryMatrix d)
    (htrace : ∑ i, matrixTraceReal d (q i) ≤ 3)
    (henergy : ∑ i, matrixCoordinateEnergy U (q i) ≤ 0) :
    ∃ V : μ → CMatrix d,
      (∀ i, IsStarProjection ((V i)ᴴ * V i)) ∧
      (∀ i, IsStarProjection (V i * (V i)ᴴ)) ∧
      (∀ i, V i * (V i)ᴴ ≤ q i) ∧
      Pairwise (fun i j => ((V i)ᴴ * V i) * ((V j)ᴴ * V j) = 0) ∧
      (∑ i, matrixCoordinateEnergy U (V i)) = 0 ∧
      (∑ i, matrixCoordinateEnergy U ((V i)ᴴ * V i)) = 0 ∧
      matrixFamilyCoverageDefect (fun i => (V i)ᴴ * V i) ≤ matrixFamilyCoverageDefect q := by
  obtain ⟨V, hV, hmin⟩ := exists_matrixOrthogonalFamilyDefect_minimizer U q
  have hbound : ∀ᶠ t : ℝ in atTop,
      matrixOrthogonalFamilyDefect U q V ≤ 78 * (Real.sqrt t)⁻¹ := by
    refine eventually_atTop.mpr ⟨1, fun t ht => ?_⟩
    obtain ⟨W, hWi, hWf, hWq, horth, he, _, hcov⟩ :=
      exists_matrixOrthogonalFamily_exponential hq U htrace
        (henergy.trans (Real.exp_pos (-16 * t)).le) ht
    have hW : W ∈ matrixOrthogonalFamilySpace q :=
      ⟨hWi, fun i => ((hWf i).le_iff_mul_eq_left (hq i)).mp (hWq i), horth⟩
    have htracecov : matrixFamilyCoverageDefect (fun i => (W i)ᴴ * W i) =
        matrixTraceReal d (1 - ∑ i, (W i)ᴴ * W i) := by
      rw [matrixFamilyCoverageDefect_orthogonal _ hWi horth]
      exact normalizedTrace_re _
    rw [htracecov] at hcov
    apply (hmin W hW).trans
    calc
      _ ≤ 74 * (Real.sqrt t)⁻¹ + 4 * (Real.sqrt t)⁻¹ :=
        add_le_add he (max_le hcov (by positivity))
      _ = _ := by ring
  have hlim : Tendsto (fun t : ℝ => 78 * (Real.sqrt t)⁻¹) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).const_mul (78 : ℝ)
  have hz := ge_of_tendsto hlim hbound
  have hnonneg : 0 ≤ ∑ i, matrixCoordinateEnergy U (V i) :=
    Finset.sum_nonneg fun i _ => matrixCoordinateEnergy_nonneg U (V i)
  have he : (∑ i, matrixCoordinateEnergy U (V i)) = 0 := by
    have hm : 0 ≤ max (matrixTraceReal d (1 - ∑ i, (V i)ᴴ * V i) -
        matrixFamilyCoverageDefect q) 0 := le_max_right _ _
    change (∑ i, matrixCoordinateEnergy U (V i)) + _ ≤ 0 at hz
    linarith
  refine ⟨V, hV.1, (fun i => matrixPartialIsometry_final_projection (hV.1 i)),
    matrixOrthogonalFamilySpace_final_le hq hV, hV.2.2, he, ?_, ?_⟩
  · apply le_antisymm _ (Finset.sum_nonneg fun i _ => matrixCoordinateEnergy_nonneg U _)
    calc
      _ ≤ ∑ i, 4 * matrixCoordinateEnergy U (V i) :=
        Finset.sum_le_sum fun i _ => matrixCoordinateEnergy_partialIsometry_initial_le U (hV.1 i)
      _ = 0 := by rw [← Finset.mul_sum, he, mul_zero]
  · have hc : matrixFamilyCoverageDefect (fun i => (V i)ᴴ * V i) =
        matrixTraceReal d (1 - ∑ i, (V i)ᴴ * V i) := by
      rw [matrixFamilyCoverageDefect_orthogonal _ hV.1 hV.2.2]
      exact normalizedTrace_re _
    have hm := le_max_left
      (matrixTraceReal d (1 - ∑ i, (V i)ᴴ * V i) - matrixFamilyCoverageDefect q) 0
    change (∑ i, matrixCoordinateEnergy U (V i)) + _ ≤ 0 at hz
    rw [hc]
    linarith

end ThomGame.Analysis
