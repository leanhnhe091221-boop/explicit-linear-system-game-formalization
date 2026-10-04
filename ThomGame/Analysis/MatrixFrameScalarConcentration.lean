module

public import ThomGame.Analysis.MatrixFrameQuotientEquivalence
public import ThomGame.Analysis.MatrixProjectionNearUnitary

/-!
# Scalar concentration survives the same negligible stabilization

The two zero extensions agree in the actual common quotient. The frame
homomorphisms are unital because their missing corners are negligible,
and injectivity restores the target's own normalized 2-norm limit.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix Filter
open scoped Topology

theorem matrixFrame_scalar_concentration_transfer {ι : Type*} (dims target large : ι → Nat)
    (F : (n : ι) → Matrix (Fin (large n)) (Fin (dims n)) ℂ)
    (G : (n : ι) → Matrix (Fin (large n)) (Fin (target n)) ℂ)
    (hF : ∀ n, (F n)ᴴ * F n = 1) (hG : ∀ n, (G n)ᴴ * G n = 1)
    (hd : ∀ n, 0 < dims n) (ht : ∀ n, 0 < target n) (hl : ∀ n, 0 < large n)
    (L : Filter ι)
    (hFd : Tendsto (fun n => (large n : ℝ) / dims n) L (𝓝 1))
    (hGt : Tendsto (fun n => (large n : ℝ) / target n) L (𝓝 1))
    (X : BoundedMatrixSequence dims) (Y : BoundedMatrixSequence target) (c : ℂ)
    (hX : Tendsto (fun n => hsNorm (X.val n - c • 1)) L (𝓝 0))
    (hXY : Tendsto (fun n => hsNorm (matrixFrameLift (F n) (X.val n) -
      matrixFrameLift (G n) (Y.val n))) L (𝓝 0)) :
    Tendsto (fun n => hsNorm (Y.val n - c • 1)) L (𝓝 0) := by
  let φ := matrixFrameQuotientHom dims large F hF hd hl L hFd
  let ψ := matrixFrameQuotientHom target large G hG ht hl L hGt
  have hx := (matrixQuotientMk_eq_iff dims L X (c • 1)).mpr hX
  have hxc : matrixQuotientMk dims L X = c • 1 := by
    change matrixQuotientMk dims L X = (matrixQuotientStarAlgHom dims L) (c • 1) at hx
    simpa only [map_smul, map_one] using hx
  have hsame : φ (matrixQuotientMk dims L X) = ψ (matrixQuotientMk target L Y) :=
    (matrixQuotientMk_eq_iff large L
      (matrixFrameSequenceLift dims large F hF X) (matrixFrameSequenceLift target large G hG Y)).mpr hXY
  have hyc : matrixQuotientMk target L Y = c • 1 := by
    apply matrixFrameQuotientHom_injective target large G hG ht hl L hGt
    change ψ (matrixQuotientMk target L Y) = ψ (c • 1)
    rw [← hsame, hxc, map_smul, map_smul, map_one, map_one]
  apply (matrixQuotientMk_eq_iff target L Y (c • 1)).mp
  change matrixQuotientMk target L Y = (matrixQuotientStarAlgHom target L) (c • 1)
  rw [map_smul, map_one, hyc]

theorem matrixFrame_scalar_concentration_transfer_eventually {ι : Type*} (dims target large : ι → Nat)
    (F : (n : ι) → Matrix (Fin (large n)) (Fin (dims n)) ℂ)
    (G : (n : ι) → Matrix (Fin (large n)) (Fin (target n)) ℂ)
    (hF : ∀ n, (F n)ᴴ * F n = 1) (hG : ∀ n, (G n)ᴴ * G n = 1)
    (hd : ∀ n, 0 < dims n) (hl : ∀ n, 0 < large n)
    (L : Filter ι) (ht : ∀ᶠ n in L, 0 < target n)
    (hFd : Tendsto (fun n => (large n : ℝ) / dims n) L (𝓝 1))
    (hGt : Tendsto (fun n => (large n : ℝ) / target n) L (𝓝 1))
    (X : BoundedMatrixSequence dims) (Y : BoundedMatrixSequence target) (c : ℂ)
    (hX : Tendsto (fun n => hsNorm (X.val n - c • 1)) L (𝓝 0))
    (hXY : Tendsto (fun n => hsNorm (matrixFrameLift (F n) (X.val n) -
      matrixFrameLift (G n) (Y.val n))) L (𝓝 0)) :
    Tendsto (fun n => hsNorm (Y.val n - c • 1)) L (𝓝 0) := by
  let φ := matrixFrameQuotientHom dims large F hF hd hl L hFd
  have hx := (matrixQuotientMk_eq_iff dims L X (c • 1)).mpr hX
  have hxc : matrixQuotientMk dims L X = c • 1 := by
    change matrixQuotientMk dims L X = (matrixQuotientStarAlgHom dims L) (c • 1) at hx
    simpa only [map_smul, map_one] using hx
  have hf : Tendsto (fun n => hsNorm (matrixFrameLift (F n) (X.val n) - c • 1)) L (𝓝 0) := by
    apply (matrixQuotientMk_eq_iff large L (matrixFrameSequenceLift dims large F hF X) (c • 1)).mp
    change φ (matrixQuotientMk dims L X) = (matrixQuotientStarAlgHom large L) (c • 1)
    rw [hxc, map_smul, map_smul, map_one, map_one]
  have hg : Tendsto (fun n => hsNorm (matrixFrameLift (G n) (Y.val n) - c • 1)) L (𝓝 0) := by
    apply squeeze_zero (fun n => hsNorm_nonneg _) _ (by simpa only [add_zero] using hXY.add hf)
    intro n
    have he := rectHSNorm_sub_triangle (large n) (matrixFrameLift (G n) (Y.val n))
      (matrixFrameLift (F n) (X.val n)) (c • 1)
    rw [rectHSNorm_sub_comm (large n) (matrixFrameLift (G n) (Y.val n))
      (matrixFrameLift (F n) (X.val n))] at he
    exact he
  have hc := (matrixFrame_complement_hsNorm_tendsto target large G hG hl L hGt).const_mul ‖c‖
  have hy : Tendsto (fun n => hsNorm (matrixFrameLift (G n) (Y.val n - c • 1))) L (𝓝 0) := by
    apply squeeze_zero (fun n => hsNorm_nonneg _) _ (by simpa only [mul_zero, add_zero] using hg.add hc)
    intro n
    have he : matrixFrameLift (G n) (Y.val n - c • 1) =
        (matrixFrameLift (G n) (Y.val n) - c • 1) + c • (1 - G n * (G n)ᴴ) := by
      rw [matrixFrameLift_sub, matrixFrameLift_smul, matrixFrameLift_one, smul_sub]
      abel
    rw [he]
    have ha := hsNorm_add_le (matrixFrameLift (G n) (Y.val n) - c • 1) (c • (1 - G n * (G n)ᴴ))
    rw [hsNorm_smul c (1 - G n * (G n)ᴴ)] at ha
    exact ha
  have hp : Tendsto (fun n => Real.sqrt ((large n : ℝ) / target n) *
      hsNorm (matrixFrameLift (G n) (Y.val n - c • 1))) L (𝓝 0) := by
    simpa only [Real.sqrt_one, mul_zero] using hGt.sqrt.mul hy
  apply hp.congr'
  exact ht.mono fun n hn => (matrixFrameLift_hsNorm_recover hn (hl n) (G n) (hG n) (Y.val n - c • 1)).symm

end ThomGame.Analysis
