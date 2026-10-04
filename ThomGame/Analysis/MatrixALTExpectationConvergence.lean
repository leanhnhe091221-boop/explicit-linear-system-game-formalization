module

public import ThomGame.Analysis.MatrixALTFiniteReconstruction
public import ThomGame.Analysis.ALTReconstructionParameters

/-!
# Actual coordinate algebras whose trace expectations approximate the channels

Large-defect coordinates are filled with the full matrix algebra. Every
coordinate contains the prescribed diagonal algebra, and the mixed-norm
error tends to zero along the original filter.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped BigOperators Topology Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra

theorem exists_matrixALT_expectation_approximation (dims : Nat → Nat) [∀ n, NeZero (dims n)]
    (μ : Nat → Type*) [∀ n, Fintype (μ n)] [∀ n, DecidableEq (μ n)]
    (F : (n : Nat) → CMatrix (dims n) →CP CMatrix (dims n))
    (hF : ∀ n, F n 1 = 1)
    (htrace : ∀ n X, normalizedTrace (F n X) = normalizedTrace X)
    (hpair : ∀ n X Y, normalizedTrace (star (F n X) * Y) = normalizedTrace (star X * F n Y))
    (E : (n : Nat) → μ n → CMatrix (dims n))
    (hE : ∀ n i, IsStarProjection (E n i)) (hne : ∀ n i, E n i ≠ 0)
    (horth : ∀ n, Pairwise (fun i j => E n i * E n j = 0)) (hsum : ∀ n, ∑ i, E n i = 1)
    (hbimod : ∀ n A X B, A ∈ matrixPartitionScalarAlgebra (E n) → B ∈ matrixPartitionScalarAlgebra (E n) →
      F n (A * X * B) = A * F n X * B)
    (L : Filter Nat) (hL : L ≤ atTop)
    (hdelta : Tendsto (fun n => matrixMixedNorm ((F n).toLinearMap.comp (F n).toLinearMap - (F n).toLinearMap)) L (𝓝 0))
    (hsigma : Tendsto (fun n => matrixScalarMixingError (E n) (F n).toLinearMap) L (𝓝 0)) :
    ∃ A : (n : Nat) → StarSubalgebra ℂ (CMatrix (dims n)),
      (∀ n, matrixPartitionScalarAlgebra (E n) ≤ A n) ∧
      Tendsto (fun n => matrixMixedNorm ((F n).toLinearMap - matrixTraceProjection (A n))) L (𝓝 0) := by
  classical
  let delta n := matrixMixedNorm ((F n).toLinearMap.comp (F n).toLinearMap - (F n).toLinearMap)
  let sigma n := matrixScalarMixingError (E n) (F n).toLinearMap
  let rho n := altReconstructionThreshold (delta n) (sigma n) n
  have hpos n : 0 < rho n := altReconstructionThreshold_pos (delta n) (sigma n) n
    (matrixMixedNorm_nonneg _) (matrixScalarMixingError_nonneg _ _)
  have hlim : Tendsto rho L (𝓝 0) := altReconstructionThreshold_tendsto delta sigma L hL hdelta hsigma
  have hex n : ∃ A : StarSubalgebra ℂ (CMatrix (dims n)), matrixPartitionScalarAlgebra (E n) ≤ A ∧
      (rho n ≤ 1 / 1024 → matrixMixedNorm ((F n).toLinearMap - matrixTraceProjection A) ≤ 134 * Real.sqrt (rho n)) := by
    by_cases hsmall : rho n ≤ 1 / 1024
    · have hb := altReconstructionThreshold_bounds (delta n) (sigma n) n
        (matrixMixedNorm_nonneg _) (matrixScalarMixingError_nonneg _ _)
      obtain ⟨A, hA, herr⟩ := exists_matrixALT_approximating_algebra (F n) (hF n) (htrace n) (hpair n)
        (E n) (hE n) (hne n) (horth n) (hsum n) (hbimod n) (rho n) (hpos n) hsmall hb.2 hb.1
      exact ⟨A, hA, fun _ => herr⟩
    · exact ⟨⊤, le_top, fun h => (hsmall h).elim⟩
  choose A hA using hex
  refine ⟨A, fun n => (hA n).1, ?_⟩
  have hsmall : ∀ᶠ n in L, rho n ≤ 1 / 1024 := hlim.eventually_le_const (by norm_num)
  apply squeeze_zero' (Eventually.of_forall (fun n => matrixMixedNorm_nonneg _))
    (hsmall.mono (fun n hn => (hA n).2 hn))
  simpa only [Real.sqrt_zero, mul_zero] using hlim.sqrt.const_mul 134

end ThomGame.Analysis
