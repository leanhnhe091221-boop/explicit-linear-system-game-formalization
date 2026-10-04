module

public import ThomGame.Analysis.FinitePairMatching
public import ThomGame.Analysis.MatrixOrthogonalRectangleSums

/-!
# Removing the endpoints of an actual bad-eigenvalue matching

The chosen contractions sum to a contraction, and the squared defects
add exactly. Consequently the removed endpoint trace is bounded by
64 times the squared actual idempotence defect divided by rho^6.
Every remaining rectangular eigenvalue is in the two required bands.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra

variable {d : Nat} [NeZero d] {μ : Type*} [Fintype μ]

def MatrixALTBadPair (F : CMatrix d →ₗ[ℂ] CMatrix d) (E : μ → CMatrix d) (rho : ℝ) (i j : μ) : Prop :=
  ∃ (lam : ℝ) (X : CMatrix d), X ≠ 0 ∧ E i * X = X ∧ X * E j = X ∧
    F X = (lam : ℂ) • X ∧ rho < |lam| ∧ rho < 1 - lam

theorem matrixALTBadPair_irrefl (F : CMatrix d →ₗ[ℂ] CMatrix d)
    (htrace : ∀ X, normalizedTrace (F X) = normalizedTrace X) (E : μ → CMatrix d)
    (rho : ℝ) (hrho : 0 < rho) (hsmall : rho ≤ 1 / 2)
    (hsigma : matrixScalarMixingError E F ≤ rho ^ 4) (i : μ) : ¬ MatrixALTBadPair F E rho i i := by
  rintro ⟨lam, X, hX, hl, hr, he, hbad, haway⟩
  exact matrixALT_no_bad_diagonal F htrace E i X hX hl hr lam rho hrho hsmall hsigma he ⟨hbad, haway⟩

theorem matrixALT_matching_endpoint_trace [DecidableEq μ]
    (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (hpair : ∀ A B, normalizedTrace (star (F A) * B) = normalizedTrace (star A * F B))
    (E : μ → CMatrix d) (hE : ∀ i, IsStarProjection (E i)) (hne : ∀ i, E i ≠ 0)
    (horth : Pairwise (fun i j => E i * E j = 0))
    (hbimod : ∀ A X B, A ∈ matrixPartitionScalarAlgebra E → B ∈ matrixPartitionScalarAlgebra E →
      F (A * X * B) = A * F X * B)
    (rho : ℝ) (hrho : 0 < rho) (hsmall : rho ≤ 1 / 2)
    (hsigma : matrixScalarMixingError E F.toLinearMap ≤ rho ^ 4)
    (M : Finset (μ × μ)) (hM : IsFinitePairMatching (MatrixALTBadPair F.toLinearMap E rho) M) :
    ∑ i ∈ finiteMatchingVertices M, (normalizedTrace (E i)).re ≤
      64 * matrixMixedNorm (F.toLinearMap.comp F.toLinearMap - F.toLinearMap) ^ 2 / rho ^ 6 := by
  classical
  have hw (e : M) : ∃ Y : CMatrix d, matrixOpNorm Y ≤ 1 ∧ E e.val.1 * Y = Y ∧ Y * E e.val.2 = Y ∧
      (((max (E e.val.1).rank (E e.val.2).rank : Nat) : ℝ) / d) * rho ^ 6 / 32 ≤ hsNorm (F (F Y) - F Y) ^ 2 := by
    obtain ⟨lam, X, hX, hl, hr, he, hbad, haway⟩ := (hM.1 e.val e.property).1
    exact exists_matrixALT_bad_rectangle_contraction F hF hpair E hE hne e.val.1 e.val.2 X hX hl hr
      lam rho hrho hsmall hsigma hbad haway he
  choose X hn hl hr hbound using hw
  have hP : Pairwise (fun e f : M => E e.val.1 * E f.val.1 = 0) := by
    intro e f hef
    exact horth (fun h => hef (finitePairMatching_fst_injective hM h))
  have hQ : Pairwise (fun e f : M => E e.val.2 * E f.val.2 = 0) := by
    intro e f hef
    exact horth (fun h => hef (finitePairMatching_snd_injective hM h))
  have hinv (e : M) (Y : CMatrix d) (hY : E e.val.1 * Y = Y) : E e.val.1 * F Y = F Y := by
    simpa only [mul_one, hY] using (hbimod (E e.val.1) Y 1
      (matrixPartitionScalarAlgebra_projection_mem E e.val.1) (matrixPartitionScalarAlgebra E).one_mem).symm
  have hd := matrixOrthogonalRectangles_defect_sum_le F.toLinearMap
    (fun e : M => E e.val.1) (fun e : M => E e.val.2) X
    (fun e => hE e.val.1) (fun e => hE e.val.2) hP hQ hl hr hn hinv
  have hm (e : M) : ((normalizedTrace (E e.val.1)).re + (normalizedTrace (E e.val.2)).re) * rho ^ 6 / 64 ≤
      hsNorm (F (F (X e)) - F (X e)) ^ 2 := by
    have ht : (normalizedTrace (E e.val.1)).re + (normalizedTrace (E e.val.2)).re ≤
        2 * (((max (E e.val.1).rank (E e.val.2).rank : Nat) : ℝ) / d) := by
      have hm : max (normalizedTrace (E e.val.1)).re (normalizedTrace (E e.val.2)).re =
          ((max (E e.val.1).rank (E e.val.2).rank : Nat) : ℝ) / d := by
        rw [matrixProjection_trace_eq_rank (hE e.val.1), matrixProjection_trace_eq_rank (hE e.val.2),
          max_div_div_right (Nat.cast_nonneg d), Nat.cast_max]
      rw [← hm]
      linarith [le_max_left (normalizedTrace (E e.val.1)).re (normalizedTrace (E e.val.2)).re,
        le_max_right (normalizedTrace (E e.val.1)).re (normalizedTrace (E e.val.2)).re]
    have hb := mul_le_mul_of_nonneg_right ht (pow_nonneg hrho.le 6)
    linarith [hbound e]
  have hs := (Finset.sum_le_sum (fun e (_ : e ∈ (Finset.univ : Finset M)) => hm e)).trans hd
  have he : ∑ i ∈ finiteMatchingVertices M, (normalizedTrace (E i)).re =
      ∑ e : M, ((normalizedTrace (E e.val.1)).re + (normalizedTrace (E e.val.2)).re) := by
    rw [finitePairMatching_endpoint_weight hM]
    exact (Finset.sum_coe_sort M (fun e => (normalizedTrace (E e.1)).re + (normalizedTrace (E e.2)).re)).symm
  rw [← Finset.sum_div, ← Finset.sum_mul, ← he] at hs
  apply (le_div_iff₀ (pow_pos hrho 6)).mpr
  linarith

theorem exists_matrixALT_retained_eigenvalue_bands
    (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ X, normalizedTrace (F X) = normalizedTrace X)
    (hpair : ∀ A B, normalizedTrace (star (F A) * B) = normalizedTrace (star A * F B))
    (E : μ → CMatrix d) (hE : ∀ i, IsStarProjection (E i)) (hne : ∀ i, E i ≠ 0)
    (horth : Pairwise (fun i j => E i * E j = 0))
    (hbimod : ∀ A X B, A ∈ matrixPartitionScalarAlgebra E → B ∈ matrixPartitionScalarAlgebra E →
      F (A * X * B) = A * F X * B)
    (rho : ℝ) (hrho : 0 < rho) (hsmall : rho ≤ 1 / 2)
    (hsigma : matrixScalarMixingError E F.toLinearMap ≤ rho ^ 4) :
    ∃ S : Finset μ,
      (∑ i ∈ S, (normalizedTrace (E i)).re ≤
        64 * matrixMixedNorm (F.toLinearMap.comp F.toLinearMap - F.toLinearMap) ^ 2 / rho ^ 6) ∧
      ∀ i ∉ S, ∀ j ∉ S, ∀ (lam : ℝ) (X : CMatrix d), X ≠ 0 → E i * X = X → X * E j = X →
        F X = (lam : ℂ) • X → (-rho ≤ lam ∧ lam ≤ rho) ∨ (1 - rho ≤ lam ∧ lam ≤ 1) := by
  classical
  obtain ⟨M, hM, hcover⟩ := exists_finitePairMatching_cover (MatrixALTBadPair F.toLinearMap E rho)
  refine ⟨finiteMatchingVertices M,
    matrixALT_matching_endpoint_trace F hF hpair E hE hne horth hbimod rho hrho hsmall hsigma M hM, ?_⟩
  intro i hi j hj lam X hX hl hr he
  have hn := matrixUCP_real_eigenvalue_abs_le_one F hF htrace lam X hX he
  by_cases hlam : |lam| ≤ rho
  · exact Or.inl (abs_le.mp hlam)
  · right
    refine ⟨?_, (le_abs_self lam).trans hn⟩
    by_contra h
    have hbad : MatrixALTBadPair F.toLinearMap E rho i j :=
      ⟨lam, X, hX, hl, hr, he, lt_of_not_ge hlam, by linarith⟩
    have hij : i ≠ j := by
      rintro rfl
      exact matrixALTBadPair_irrefl F.toLinearMap htrace E rho hrho hsmall hsigma i hbad
    exact (hcover i j hbad hij).elim hi hj

end ThomGame.Analysis
