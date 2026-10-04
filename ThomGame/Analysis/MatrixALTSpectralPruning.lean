module

public import ThomGame.Analysis.MatrixRetainedBlockProjection
public import ThomGame.Analysis.MatrixRectangleSpectrum

/-!
# Actual coordinate spectral pruning for ALT (5.5)

The two error sequences are the actual scalar-corner and idempotence
operator norms. Their convergence constructs positive thresholds and
retained original block sums with missing trace tending to zero.
The eigenvalue bands hold eventually, with no matching or clipping
witness assumed as input.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped BigOperators Topology Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra

theorem exists_matrixALT_spectral_pruning (dims : Nat → Nat) [∀ n, NeZero (dims n)]
    (μ : Nat → Type*) [∀ n, Fintype (μ n)] [∀ n, DecidableEq (μ n)]
    (F : (n : Nat) → CMatrix (dims n) →CP CMatrix (dims n))
    (hF : ∀ n, F n 1 = 1)
    (htrace : ∀ n X, normalizedTrace (F n X) = normalizedTrace X)
    (hpair : ∀ n A B, normalizedTrace (star (F n A) * B) = normalizedTrace (star A * F n B))
    (E : (n : Nat) → μ n → CMatrix (dims n))
    (hE : ∀ n i, IsStarProjection (E n i)) (hne : ∀ n i, E n i ≠ 0)
    (horth : ∀ n, Pairwise (fun i j => E n i * E n j = 0)) (hsum : ∀ n, ∑ i, E n i = 1)
    (hbimod : ∀ n A X B, A ∈ matrixPartitionScalarAlgebra (E n) → B ∈ matrixPartitionScalarAlgebra (E n) →
      F n (A * X * B) = A * F n X * B)
    (L : Filter Nat) (hL : L ≤ atTop)
    (hdelta : Tendsto (fun n => matrixMixedNorm ((F n).toLinearMap.comp (F n).toLinearMap - (F n).toLinearMap)) L (𝓝 0))
    (hsigma : Tendsto (fun n => matrixScalarMixingError (E n) (F n).toLinearMap) L (𝓝 0)) :
    let rho := fun n => altReconstructionThreshold
      (matrixMixedNorm ((F n).toLinearMap.comp (F n).toLinearMap - (F n).toLinearMap))
      (matrixScalarMixingError (E n) (F n).toLinearMap) n
    (∀ n, 0 < rho n) ∧ Tendsto rho L (𝓝 0) ∧
    ∃ S : (n : Nat) → Finset (μ n),
      (∀ n, IsStarProjection (matrixRetainedBlockProjection (E n) (S n))) ∧
      (∀ n, matrixRetainedBlockProjection (E n) (S n) = ∑ i ∈ Finset.univ \ S n, E n i) ∧
      Tendsto (fun n => (normalizedTrace (1 - matrixRetainedBlockProjection (E n) (S n))).re) L (𝓝 0) ∧
      ∀ᶠ n in L,
        (normalizedTrace (1 - matrixRetainedBlockProjection (E n) (S n))).re ≤ 64 * rho n ^ 2 ∧
        (∀ i ∉ S n, ∀ j ∉ S n, ∀ (lam : ℝ) (X : CMatrix (dims n)), X ≠ 0 → E n i * X = X → X * E n j = X →
          F n X = (lam : ℂ) • X → (-rho n ≤ lam ∧ lam ≤ rho n) ∨ (1 - rho n ≤ lam ∧ lam ≤ 1)) ∧
        ∀ i ∉ S n, ∀ j ∉ S n,
          spectrum ℂ (matrixScalarBimoduleRectangleMap (F n).toLinearMap (E n) (hbimod n) i j).toLinearMap ⊆
            Complex.ofReal '' (Set.Icc (-rho n) (rho n) ∪ Set.Icc (1 - rho n) 1) := by
  classical
  let delta n := matrixMixedNorm ((F n).toLinearMap.comp (F n).toLinearMap - (F n).toLinearMap)
  let sigma n := matrixScalarMixingError (E n) (F n).toLinearMap
  let rho n := altReconstructionThreshold (delta n) (sigma n) n
  change (∀ n, 0 < rho n) ∧ Tendsto rho L (𝓝 0) ∧ _
  have hpos (n : Nat) : 0 < rho n := altReconstructionThreshold_pos (delta n) (sigma n) n
    (matrixMixedNorm_nonneg _) (matrixScalarMixingError_nonneg _ _)
  have hlim : Tendsto rho L (𝓝 0) := altReconstructionThreshold_tendsto delta sigma L hL hdelta hsigma
  refine ⟨hpos, hlim, ?_⟩
  have hex (n : Nat) : ∃ S : Finset (μ n), rho n ≤ 1 / 2 →
      (normalizedTrace (1 - matrixRetainedBlockProjection (E n) S)).re ≤ 64 * rho n ^ 2 ∧
      ∀ i ∉ S, ∀ j ∉ S, ∀ (lam : ℝ) (X : CMatrix (dims n)), X ≠ 0 → E n i * X = X → X * E n j = X →
        F n X = (lam : ℂ) • X → (-rho n ≤ lam ∧ lam ≤ rho n) ∨ (1 - rho n ≤ lam ∧ lam ≤ 1) := by
    by_cases hsmall : rho n ≤ 1 / 2
    · have hb := altReconstructionThreshold_bounds (delta n) (sigma n) n
        (matrixMixedNorm_nonneg _) (matrixScalarMixingError_nonneg _ _)
      obtain ⟨S, p, hp, _, _, ht, hbands⟩ := exists_matrixALT_retained_projection
        (F n) (hF n) (htrace n) (hpair n) (E n) (hE n) (hne n) (horth n) (hsum n) (hbimod n)
        (rho n) (hpos n) hsmall hb.2 hb.1
      exact ⟨S, fun _ => ⟨hp ▸ ht, hbands⟩⟩
    · exact ⟨∅, fun h => (hsmall h).elim⟩
  choose S hS using hex
  have hev := (altReconstructionThreshold_eventually_small delta sigma L hL hdelta hsigma).mono
    (fun n hn => hS n hn)
  have hev' := hev.mono (fun n h => And.intro h.1 (And.intro h.2
    (fun i hi j hj => matrixScalarBimoduleRectangleMap_spectrum_bands (F n).toLinearMap (E n)
      (hbimod n) (hpair n) i j (rho n) (h.2 i hi j hj))))
  refine ⟨S, fun n => matrixRetainedBlockProjection_isStarProjection (E n) (S n) (hE n) (horth n),
    fun n => matrixRetainedBlockProjection_sum (E n) (S n) (hsum n), ?_, hev'⟩
  apply squeeze_zero' (Eventually.of_forall (fun n => ?_)) (hev.mono (fun _ h => h.1))
    (by simpa only [zero_pow (by norm_num : 2 ≠ 0), mul_zero] using (hlim.pow 2).const_mul 64)
  exact (Complex.nonneg_iff.mp (normalizedTrace_nonneg _
    (matrixRetainedBlockProjection_isStarProjection (E n) (S n) (hE n) (horth n)).one_sub.nonneg)).1

end ThomGame.Analysis
