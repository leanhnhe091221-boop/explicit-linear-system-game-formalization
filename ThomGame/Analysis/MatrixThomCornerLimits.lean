module

public import ThomGame.Analysis.MatrixThomCornerApproximation

/-!
# Vanishing corner-compression and round-trip errors

The bounds are independent of the chosen contraction sequences and use
the original dimensions even on the corrected spaces.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} (dims : ι → Nat) [∀ n, NeZero (dims n)]
    {A B D : (n : ι) → StarSubalgebra ℂ (CMatrix (dims n))} {ε : ι → ℝ}
    (S : (n : ι) → MatrixThomSpectralData (A n) (B n) (D n) (ε n))
    (hε0 : ∀ n, 0 ≤ ε n) {L : Filter ι}

include hε0

theorem matrixThom_source_compression_tendsto (hε : Filter.Tendsto ε L (𝓝 0))
    (X : (n : ι) → CMatrix (dims n)) (hX : ∀ n, matrixOpNorm (X n) ≤ 1) :
    Filter.Tendsto (fun n => rectHSNorm (dims n)
      (X n - ((S n).cutPolarᴴ * (S n).cutPolar) * X n * ((S n).cutPolarᴴ * (S n).cutPolar)))
      L (𝓝 0) := by
  exact squeeze_zero (fun n => rectHSNorm_nonneg _ _)
    (fun n => (S n).cutPolar_source_compression_loss (hε0 n) (X n) (hX n))
    (by simpa using hε.const_mul 2)

theorem matrixThom_target_compression_tendsto (hε : Filter.Tendsto ε L (𝓝 0))
    (Y : (n : ι) → CMatrix (S n).cut.rank) (hY : ∀ n, matrixOpNorm (Y n) ≤ 1) :
    Filter.Tendsto (fun n => rectHSNorm (dims n)
      (Y n - ((S n).cutPolar * (S n).cutPolarᴴ) * Y n * ((S n).cutPolar * (S n).cutPolarᴴ)))
      L (𝓝 0) := by
  exact squeeze_zero (fun n => rectHSNorm_nonneg _ _)
    (fun n => (S n).cutPolar_target_compression_loss (hε0 n) (Y n) (hY n))
    (by simpa using hε.const_mul (2 * Real.sqrt 2))

theorem matrixThom_source_roundtrip_tendsto (hε : Filter.Tendsto ε L (𝓝 0))
    (X : (n : ι) → CMatrix (dims n)) (hX : ∀ n, matrixOpNorm (X n) ≤ 1) :
    Filter.Tendsto (fun n => rectHSNorm (dims n)
      (X n - (S n).cutPolarᴴ * ((S n).cutPolar * X n * (S n).cutPolarᴴ) * (S n).cutPolar))
      L (𝓝 0) := by
  simpa only [Matrix.mul_assoc] using matrixThom_source_compression_tendsto dims S hε0 hε X hX

theorem matrixThom_target_roundtrip_tendsto (hε : Filter.Tendsto ε L (𝓝 0))
    (Y : (n : ι) → CMatrix (S n).cut.rank) (hY : ∀ n, matrixOpNorm (Y n) ≤ 1) :
    Filter.Tendsto (fun n => rectHSNorm (dims n)
      (Y n - (S n).cutPolar * ((S n).cutPolarᴴ * Y n * (S n).cutPolar) * (S n).cutPolarᴴ))
      L (𝓝 0) := by
  simpa only [Matrix.mul_assoc] using matrixThom_target_compression_tendsto dims S hε0 hε Y hY

end ThomGame.Analysis
