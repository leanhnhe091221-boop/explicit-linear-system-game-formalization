module

public import ThomGame.Analysis.MatrixProjectionRankSums
public import ThomGame.Analysis.MatrixScalarCornerMass

/-!
# Dimension-free trace loss for a family of subprojections

Uniform relative loss on orthogonal blocks adds without a factor
depending on the number of blocks.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat} [NeZero d] {μ : Type*} [Fintype μ]

theorem matrixSubprojection_sum_trace_loss (E q : μ → CMatrix d)
    (hE : ∀ i, IsStarProjection (E i)) (hq : ∀ i, IsStarProjection (q i))
    (horth : Pairwise (fun i j => E i * E j = 0)) (hle : ∀ i, q i ≤ E i)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hmass : ∀ i, (1 - epsilon) * (normalizedTrace (E i)).re ≤ (normalizedTrace (q i)).re) :
    IsStarProjection (∑ i, q i) ∧ (∑ i, q i) ≤ (∑ i, E i) ∧
      (normalizedTrace (1 - ∑ i, q i)).re ≤ (normalizedTrace (1 - ∑ i, E i)).re + epsilon := by
  have hqorth : Pairwise (fun i j => q i * q j = 0) := by
    intro i j hij
    exact matrixProjection_subprojections_orthogonal (hq i) (hq j) (hE i) (hE j)
      (hle i) (hle j) (horth hij)
  have hp := matrixProjection_sum E hE horth
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hmass i)
  rw [← Finset.mul_sum] at hsum
  have hp1 : (normalizedTrace (∑ i, E i)).re ≤ 1 := by
    have h := (Complex.nonneg_iff.mp (normalizedTrace_nonneg _ hp.one_sub_nonneg)).1
    simpa only [normalizedTrace_sub, normalizedTrace_one, Complex.sub_re, Complex.one_re,
      sub_nonneg] using h
  have hsmall := mul_le_mul_of_nonneg_left hp1 hepsilon
  simp only [normalizedTrace_sum, Complex.re_sum] at hp1 hsmall
  refine ⟨matrixProjection_sum q hq hqorth, Finset.sum_le_sum (fun i _ => hle i), ?_⟩
  simp only [normalizedTrace_sub, normalizedTrace_one, normalizedTrace_sum,
    Complex.sub_re, Complex.one_re, Complex.re_sum]
  nlinarith

end ThomGame.Analysis
