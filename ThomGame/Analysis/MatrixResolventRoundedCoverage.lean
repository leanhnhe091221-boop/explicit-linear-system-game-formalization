module

public import ThomGame.Analysis.MatrixResolventSpectralRounding

/-!
# Coverage of the actual rounded resolvent family

Every threshold in [gamma,2 gamma] gives the rank, weighted trace and
coverage conclusions. The positive-part rounding error is proved
from the input projection traces; it is no longer a hypothesis.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {d : Nat} {γ s : ℝ} {P : CMatrix d}

theorem matrixResolventSpectralProjection_rounding_gamma_le (hγ : 0 < γ) (hP : IsStarProjection P)
    (F : Nat → CMatrix d) (hF : ∀ i, IsStarProjection (F i)) (n : Nat)
    (htrace : (∑ i ∈ Finset.range n, (normalizedTrace (F i)).re) ≤ 3)
    (hs : s ∈ Set.Icc γ (2 * γ)) :
    (∑ i : Fin n, (normalizedTrace (matrixResolventDifferenceFamily (γ ^ 2) P F i -
      matrixResolventSpectralProjection (γ ^ 2) P F s i)⁺).re) ≤ 6 * γ := by
  have ht0 : 0 ≤ ∑ i ∈ Finset.range n, (normalizedTrace (F i)).re :=
    Finset.sum_nonneg fun i _ => (Complex.nonneg_iff.mp (normalizedTrace_nonneg _ (hF i).nonneg)).1
  have he := matrixResolventSpectralProjection_rounding_sum_le (sq_pos_of_pos hγ) hP.nonneg F hF
    (hγ.le.trans hs.1) n
  have hb := mul_le_mul hs.2 htrace ht0 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hγ.le)
  linarith

theorem matrixResolventSpectralProjection_weighted_gamma_le (hγ : 0 < γ) (hP : IsStarProjection P)
    (F : Nat → CMatrix d) (hF : ∀ i, IsStarProjection (F i)) (n : Nat)
    (htrace : (∑ i ∈ Finset.range n, (normalizedTrace (F i)).re) ≤ 3)
    (hs : s ∈ Set.Icc γ (2 * γ)) :
    (∑ i : Fin n, (normalizedTrace (matrixProjectionPartialSum P F i ^ 2 *
      matrixResolventSpectralProjection (γ ^ 2) P F s i)).re) ≤ 3 * γ := by
  have hs0 : 0 < s := hγ.trans_le hs.1
  have ht0 : 0 ≤ ∑ i ∈ Finset.range n, (normalizedTrace (F i)).re :=
    Finset.sum_nonneg fun i _ => (Complex.nonneg_iff.mp (normalizedTrace_nonneg _ (hF i).nonneg)).1
  have he := matrixResolventSpectralProjection_weighted_trace_sum_le (sq_pos_of_pos hγ) hP.nonneg F hF hs0 n
  have hcoef : s⁻¹ * γ ^ 2 ≤ γ := by
    rw [mul_comm, ← div_eq_mul_inv]
    apply (div_le_iff₀ hs0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hs.1 hγ.le]
  have hb := mul_le_mul hcoef htrace ht0 hγ.le
  linarith

theorem matrixResolventSpectralProjection_coverage [NeZero d] (hγ : 0 < γ) (hP : IsStarProjection P)
    (F : Nat → CMatrix d) (hF : ∀ i, IsStarProjection (F i)) (n : Nat)
    (htrace : (∑ i ∈ Finset.range n, (normalizedTrace (F i)).re) ≤ 3)
    (hs : s ∈ Set.Icc γ (2 * γ)) :
    matrixFamilyCoverageDefect (fun i : Fin n => matrixResolventSpectralProjection (γ ^ 2) P F s i) ≤
      (normalizedTrace P).re +
      (normalizedTrace (1 - matrixSpectralCut (matrixProjectionPartialSum P F n) γ)).re + 7 * γ :=
  matrixResolventFamily_coverage_of_rounding hγ hP F hF n _
    (fun i => matrixResolventSpectralProjection_isStarProjection (sq_pos_of_pos hγ) hP.nonneg F hF s i)
    (matrixResolventSpectralProjection_rounding_gamma_le hγ hP F hF n htrace hs)

end ThomGame.Analysis
