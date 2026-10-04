module

public import ThomGame.Analysis.MatrixFrameScalarConcentration
public import ThomGame.Analysis.MatrixThomStableUnitaryTransport
public import ThomGame.Analysis.MatrixThomCorrectedStabilization

/-!
# Scalar limits through the actual common Thom transport

The same unitary completion identifies the two zero extensions. Positive
corrected dimensions and both actual dimension ratios supply the unital
quotient maps, so concentration is recovered at the corrected denominator.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix Filter
open scoped Topology

theorem hsNorm_unitaryPullback_sub_scalar {d : Nat} (U : UnitaryMatrix d) (X : CMatrix d) (c : ℂ) :
    hsNorm (U.valᴴ * X * U.val - c • 1) = hsNorm (X - c • 1) := by
  have hunit : U.valᴴ * U.val = 1 := U.prop.1
  have he : U.valᴴ * (X - c • 1) * U.val = U.valᴴ * X * U.val - c • 1 := by
    rw [mul_sub, sub_mul, mul_smul_comm, mul_one, smul_mul_assoc, hunit]
  rw [← he, hsNorm_mul_unitary]
  exact hsNorm_unitary_mul U⁻¹ _

theorem matrixThom_scalar_transport_tendsto {ι : Type*} (dims : ι → Nat) [∀ n, NeZero (dims n)]
    {A B D : (n : ι) → StarSubalgebra ℂ (CMatrix (dims n))} {ε : ι → ℝ}
    (S : (n : ι) → MatrixThomSpectralData (A n) (B n) (D n) (ε n))
    (hm : ∀ n, 0 < (S n).cut.rank) (L : Filter ι) (hε : Tendsto ε L (𝓝 0))
    (X : BoundedMatrixSequence dims) (Y : BoundedMatrixSequence (fun n => (S n).cut.rank)) (c : ℂ)
    (hX : Tendsto (fun n => hsNorm (X.val n - c • 1)) L (𝓝 0))
    (hXY : Tendsto (fun n => rectHSNorm (S n).stableDim
      (matrixFrameLift (S n).stableTargetFrame (Y.val n) * (S n).stableUnitary.val -
        (S n).stableUnitary.val * matrixFrameLift (S n).stableSourceCoordinateFrame (X.val n)))
      L (𝓝 0)) : Tendsto (fun n => hsNorm (Y.val n - c • 1)) L (𝓝 0) := by
  apply matrixFrame_scalar_concentration_transfer dims (fun n => (S n).cut.rank) (fun n => (S n).stableDim)
    (fun n => (S n).stableSourceFrame) (fun n => (S n).stableTargetFrame)
    (fun n => (S n).stableSourceFrame_initial) (fun n => (S n).stableTargetFrame_initial)
    (fun n => NeZero.pos (dims n)) hm (fun n => (NeZero.pos (dims n)).trans_le (S n).le_stableDim) L
    (matrixThom_stable_dimension_ratio_tendsto dims S hε)
    (matrixThom_stable_to_cut_ratio_tendsto dims S L hε hm) X Y c hX
  apply hXY.congr'
  exact Eventually.of_forall fun n => (S n).stableUnitary_transport_norm _ _ _

theorem matrixThom_stable_to_cut_ratio_tendsto_general {ι : Type*} (dims : ι → Nat) [∀ n, NeZero (dims n)]
    {A B D : (n : ι) → StarSubalgebra ℂ (CMatrix (dims n))} {ε : ι → ℝ}
    (S : (n : ι) → MatrixThomSpectralData (A n) (B n) (D n) (ε n))
    (L : Filter ι) (hε : Tendsto ε L (𝓝 0)) :
    Tendsto (fun n => ((S n).stableDim : ℝ) / (S n).cut.rank) L (𝓝 1) := by
  have hr := (matrixThom_stable_dimension_ratio_tendsto dims S hε).div
    (matrixThom_cut_dimension_ratio_tendsto dims S hε) one_ne_zero
  have hr' : Tendsto (fun n => (((S n).stableDim : ℝ) / dims n) /
      (((S n).cut.rank : ℝ) / dims n)) L (𝓝 1) := by
    simpa only [Pi.div_def, div_self one_ne_zero] using hr
  exact hr'.congr' (Eventually.of_forall fun n =>
    div_div_div_cancel_right₀ (Nat.cast_ne_zero.mpr (NeZero.ne (dims n)) : (dims n : ℝ) ≠ 0) _ _)

theorem matrixThom_scalar_transport_tendsto_general {ι : Type*} (dims : ι → Nat) [∀ n, NeZero (dims n)]
    {A B D : (n : ι) → StarSubalgebra ℂ (CMatrix (dims n))} {ε : ι → ℝ}
    (S : (n : ι) → MatrixThomSpectralData (A n) (B n) (D n) (ε n))
    (L : Filter ι) (hε : Tendsto ε L (𝓝 0))
    (X : BoundedMatrixSequence dims) (Y : BoundedMatrixSequence (fun n => (S n).cut.rank)) (c : ℂ)
    (hX : Tendsto (fun n => hsNorm (X.val n - c • 1)) L (𝓝 0))
    (hXY : Tendsto (fun n => rectHSNorm (S n).stableDim
      (matrixFrameLift (S n).stableTargetFrame (Y.val n) * (S n).stableUnitary.val -
        (S n).stableUnitary.val * matrixFrameLift (S n).stableSourceCoordinateFrame (X.val n)))
      L (𝓝 0)) : Tendsto (fun n => hsNorm (Y.val n - c • 1)) L (𝓝 0) := by
  have hm : ∀ᶠ n in L, 0 < (S n).cut.rank := by
    have hp := (matrixThom_cut_dimension_ratio_tendsto dims S hε).eventually (eventually_gt_nhds zero_lt_one)
    filter_upwards [hp] with n hn
    by_contra h
    have hz := Nat.eq_zero_of_not_pos h
    simp only [hz, Nat.cast_zero, zero_div, lt_self_iff_false] at hn
  apply matrixFrame_scalar_concentration_transfer_eventually dims (fun n => (S n).cut.rank)
    (fun n => (S n).stableDim) (fun n => (S n).stableSourceFrame) (fun n => (S n).stableTargetFrame)
    (fun n => (S n).stableSourceFrame_initial) (fun n => (S n).stableTargetFrame_initial)
    (fun n => NeZero.pos (dims n)) (fun n => (NeZero.pos (dims n)).trans_le (S n).le_stableDim) L hm
    (matrixThom_stable_dimension_ratio_tendsto dims S hε)
    (matrixThom_stable_to_cut_ratio_tendsto_general dims S L hε) X Y c hX
  apply hXY.congr'
  exact Eventually.of_forall fun n => (S n).stableUnitary_transport_norm _ _ _

end ThomGame.Analysis
