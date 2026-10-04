module

public import ThomGame.Analysis.MatrixALTBadMatching
public import ThomGame.Analysis.ALTReconstructionParameters

/-!
# The actual retained block projection in ALT reconstruction

Deleting matching endpoints gives the sum of the remaining original
blocks. Its missing trace has the absolute bound 64 rho^2.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra

variable {d : Nat} {μ : Type*}

noncomputable def matrixRetainedBlockProjection (E : μ → CMatrix d) (S : Finset μ) : CMatrix d :=
  1 - ∑ i ∈ S, E i

theorem matrixRetainedBlockProjection_isStarProjection (E : μ → CMatrix d) (S : Finset μ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0)) :
    IsStarProjection (matrixRetainedBlockProjection E S) := by
  have hp := matrixProjection_sum (fun i : S => E i.val) (fun i => hE i.val)
    (fun i j hij => horth (fun he => hij (Subtype.ext he)))
  rw [Finset.sum_coe_sort] at hp
  exact hp.one_sub

theorem matrixRetainedBlockProjection_trace (E : μ → CMatrix d) (S : Finset μ) :
    (normalizedTrace (1 - matrixRetainedBlockProjection E S)).re = ∑ i ∈ S, (normalizedTrace (E i)).re := by
  rw [matrixRetainedBlockProjection, sub_sub_cancel, normalizedTrace_sum, Complex.re_sum]

theorem matrixRetainedBlockProjection_sum [Fintype μ] [DecidableEq μ]
    (E : μ → CMatrix d) (S : Finset μ) (hsum : ∑ i, E i = 1) :
    matrixRetainedBlockProjection E S = ∑ i ∈ Finset.univ \ S, E i := by
  rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ S), hsum]
  rfl

theorem matrixRetainedBlockProjection_mul_block [DecidableEq μ]
    (E : μ → CMatrix d) (S : Finset μ) (hE : ∀ i, IsStarProjection (E i))
    (horth : Pairwise (fun i j => E i * E j = 0)) (i : μ) :
    matrixRetainedBlockProjection E S * E i = if i ∈ S then 0 else E i := by
  rw [matrixRetainedBlockProjection, sub_mul, one_mul, Finset.sum_mul]
  by_cases hi : i ∈ S
  · rw [ite_eq_left hi, Finset.sum_eq_single i, (hE i).isIdempotentElem.eq, sub_self]
    · intro j _ hji
      exact horth hji
    · exact fun h => (h hi).elim
  · rw [ite_eq_right hi, Finset.sum_eq_zero, sub_zero]
    intro j hj
    exact horth (fun hji => hi (hji ▸ hj))

theorem exists_matrixALT_retained_projection [NeZero d] [Fintype μ] [DecidableEq μ]
    (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ X, normalizedTrace (F X) = normalizedTrace X)
    (hpair : ∀ A B, normalizedTrace (star (F A) * B) = normalizedTrace (star A * F B))
    (E : μ → CMatrix d) (hE : ∀ i, IsStarProjection (E i)) (hne : ∀ i, E i ≠ 0)
    (horth : Pairwise (fun i j => E i * E j = 0)) (hsum : ∑ i, E i = 1)
    (hbimod : ∀ A X B, A ∈ matrixPartitionScalarAlgebra E → B ∈ matrixPartitionScalarAlgebra E →
      F (A * X * B) = A * F X * B)
    (rho : ℝ) (hrho : 0 < rho) (hsmall : rho ≤ 1 / 2)
    (hsigma : matrixScalarMixingError E F.toLinearMap ≤ rho ^ 4)
    (hdelta : matrixMixedNorm (F.toLinearMap.comp F.toLinearMap - F.toLinearMap) ≤ rho ^ 4) :
    ∃ S : Finset μ, ∃ p : CMatrix d,
      p = matrixRetainedBlockProjection E S ∧ p = ∑ i ∈ Finset.univ \ S, E i ∧ IsStarProjection p ∧
      (normalizedTrace (1 - p)).re ≤ 64 * rho ^ 2 ∧
      ∀ i ∉ S, ∀ j ∉ S, ∀ (lam : ℝ) (X : CMatrix d), X ≠ 0 → E i * X = X → X * E j = X →
        F X = (lam : ℂ) • X → (-rho ≤ lam ∧ lam ≤ rho) ∨ (1 - rho ≤ lam ∧ lam ≤ 1) := by
  obtain ⟨S, ht, hbands⟩ := exists_matrixALT_retained_eigenvalue_bands F hF htrace hpair E hE hne horth
    hbimod rho hrho hsmall hsigma
  refine ⟨S, matrixRetainedBlockProjection E S, rfl, matrixRetainedBlockProjection_sum E S hsum,
    matrixRetainedBlockProjection_isStarProjection E S hE horth, ?_, hbands⟩
  rw [matrixRetainedBlockProjection_trace]
  exact ht.trans (alt_reconstruction_removal_cost _ rho (matrixMixedNorm_nonneg _) hrho hdelta)

end ThomGame.Analysis
