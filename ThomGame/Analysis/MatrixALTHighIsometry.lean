module

public import ThomGame.Analysis.MatrixALTHighEquivalence
public import ThomGame.Analysis.MatrixProjectionIntermediateRank

/-!
# A high partial isometry with full smaller initial corner

The minimum-rank polar completion fills the smaller corner exactly.
Its energy is bounded in terms of that corner's original normalized
trace. Equal indices use the actual block projection.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat} [NeZero d]

theorem exists_matrixUCP_high_smaller_isometry {μ : Type*} [Fintype μ]
    (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ Z, normalizedTrace (F Z) = normalizedTrace Z)
    (hpair : ∀ X Y, normalizedTrace (star (F X) * Y) = normalizedTrace (star X * F Y))
    (E : μ → CMatrix d) (hE : ∀ i, IsStarProjection (E i)) (hne : ∀ i, E i ≠ 0)
    (hbimod : ∀ A X B, A ∈ matrixPartitionScalarAlgebra E → B ∈ matrixPartitionScalarAlgebra E →
      F (A * X * B) = A * F X * B)
    (i j : μ) (hji : (E j).rank ≤ (E i).rank)
    (rho : ℝ) (hrho : 0 ≤ rho) (hsmall : rho ≤ 1 / 1024)
    (hsigma : matrixScalarMixingError E F.toLinearMap ≤ rho ^ 4)
    (hbands : ∀ (lam : ℝ) (X : CMatrix d), X ≠ 0 → E i * X = X → X * E j = X →
      F X = (lam : ℂ) • X → (-rho ≤ lam ∧ lam ≤ rho) ∨ (1 - rho ≤ lam ∧ lam ≤ 1))
    (hhigh : matrixRectangleHasHighEigenvalue F.toLinearMap (E i) (E j) rho) :
    ∃ U : CMatrix d, E i * U = U ∧ U * E j = U ∧ star U * U = E j ∧
      IsStarProjection (U * star U) ∧ U * star U ≤ E i ∧
      (U * star U).rank = (E j).rank ∧ matrixOpNorm U ≤ 1 ∧
      matrixChannelEnergy F.toLinearMap U ≤ 36 * rho * (normalizedTrace (E j)).re ∧
      (1 - 2 * rho) * (normalizedTrace (E i)).re ≤ (normalizedTrace (E j)).re ∧
      (i = j → U = E i) := by
  classical
  by_cases hij : i = j
  · subst j
    have hgram : star (E i) * E i = E i := by
      rw [(hE i).isSelfAdjoint.star_eq, (hE i).isIdempotentElem.eq]
    have hfinal : E i * star (E i) = E i := by
      rw [(hE i).isSelfAdjoint.star_eq, (hE i).isIdempotentElem.eq]
    have hfix := matrixBimodule_fixes_projection F.toLinearMap hF E hbimod i
    have henergy : matrixChannelEnergy F.toLinearMap (E i) = 0 := by
      simp only [matrixChannelEnergy, hfix, normalizedTrace_gram, Complex.ofReal_re, sub_self]
    have ht := (matrixProjection_trace_re_pos (hE i) (hne i)).le
    refine ⟨E i, (hE i).isIdempotentElem.eq, (hE i).isIdempotentElem.eq, hgram,
      hfinal.symm ▸ hE i, hfinal.le, congrArg Matrix.rank hfinal,
      matrixPartialIsometry_norm_le_one (hgram.symm ▸ hE i), ?_, ?_, fun _ => rfl⟩
    · rw [henergy]
      positivity
    · nlinarith [mul_nonneg hrho ht]
  · have hinv := matrixBimodule_rectangle_invariant (matrixPartitionScalarAlgebra E) F.toLinearMap
      hbimod (E i) (E j) (matrixPartitionScalarAlgebra_projection_mem E i)
        (matrixPartitionScalarAlgebra_projection_mem E j)
    obtain ⟨U, hUl, hUr, _, hUi, hUf, hUiQ, hUfP, hUir, hUfr, hUn, heU, hrU, _⟩ :=
      exists_matrixUCP_high_rectangle_approximation F hF htrace hpair E hE hne i j hinv
        rho hrho hsmall hsigma hbands hhigh
    rw [min_eq_right hji] at hUir hUfr hrU
    rw [max_eq_left hji] at heU hrU
    have heq := matrixProjection_eq_of_le_rank_eq hUi (hE j) hUiQ hUir
    have hpos : (0 : ℝ) < (E i).rank := Nat.cast_pos.mpr (matrixProjection_rank_pos (hE i) (hne i))
    have hr := (le_div_iff₀ hpos).mp hrU
    have hrsmall := mul_le_mul_of_nonneg_right hsmall hpos.le
    have htwice : ((E i).rank : ℝ) ≤ 2 * ((E j).rank : ℝ) := by nlinarith
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have ht := div_le_div_of_nonneg_right htwice hd
    have hr' := div_le_div_of_nonneg_right hr hd
    rw [mul_div_assoc] at ht hr'
    refine ⟨U, hUl, hUr, heq, hUf, hUfP, hUfr, hUn, ?_, ?_, fun h => (hij h).elim⟩
    · rw [matrixProjection_trace_eq_rank (hE j)]
      have hh := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 18 * rho)
      nlinarith
    · simpa only [matrixProjection_trace_eq_rank (hE i), matrixProjection_trace_eq_rank (hE j)] using hr'

end ThomGame.Analysis
