module

public import ThomGame.Analysis.MatrixFrameSequences
public import ThomGame.Analysis.MatrixTracialAlgebra

/-!
# Null ideals and negligible complements under asymptotic frame embeddings

The dimension ratio tending to one makes the two normalized HS null
conditions equivalent. Every bounded target sequence agrees in its
tracial quotient with the lift of its actual compression.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix Filter
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} (dims large : ι → Nat)
    (F : (i : ι) → Matrix (Fin (large i)) (Fin (dims i)) ℂ)
    (hF : ∀ i, (F i)ᴴ * F i = 1) (hd : ∀ i, 0 < dims i) (hN : ∀ i, 0 < large i)
    (L : Filter ι) (hratio : Tendsto (fun i => (large i : ℝ) / dims i) L (𝓝 1))

include hratio in
theorem matrixDimensionRatio_inverse_tendsto :
    Tendsto (fun i => (dims i : ℝ) / large i) L (𝓝 1) := by
  simpa only [inv_div, inv_one] using hratio.inv₀ one_ne_zero

include hF hN hratio in
theorem matrixFrame_complement_hsNorm_tendsto :
    Tendsto (fun i => hsNorm (1 - F i * (F i)ᴴ)) L (𝓝 0) := by
  have he : (fun i => hsNorm (1 - F i * (F i)ᴴ)) =
      (fun i => Real.sqrt (1 - (dims i : ℝ) / large i)) :=
    funext fun i => matrixFrame_complement_hsNorm (hN i) (F i) (hF i)
  rw [he]
  have h1 : Tendsto (fun _ : ι => (1 : ℝ)) L (𝓝 1) := tendsto_const_nhds
  simpa using (h1.sub (matrixDimensionRatio_inverse_tendsto dims large L hratio)).sqrt

include hd hN hratio in
theorem matrixFrameSequenceLift_null (A : BoundedMatrixSequence dims)
    (hA : A ∈ matrixNullIdeal dims L) :
    matrixFrameSequenceLift dims large F hF A ∈ matrixNullIdeal large L := by
  change Tendsto (fun i => hsNorm (A.val i)) L (𝓝 0) at hA
  change Tendsto (fun i => hsNorm (matrixFrameLift (F i) (A.val i))) L (𝓝 0)
  have he : (fun i => hsNorm (matrixFrameLift (F i) (A.val i))) =
      (fun i => Real.sqrt ((dims i : ℝ) / large i) * hsNorm (A.val i)) :=
    funext fun i => matrixFrameLift_hsNorm_rescale (hd i) (hN i) (F i) (hF i) (A.val i)
  rw [he]
  simpa using (matrixDimensionRatio_inverse_tendsto dims large L hratio).sqrt.mul hA

include hd hN hratio in
theorem matrixFrameSequenceLift_null_iff (A : BoundedMatrixSequence dims) :
    matrixFrameSequenceLift dims large F hF A ∈ matrixNullIdeal large L ↔ A ∈ matrixNullIdeal dims L := by
  constructor
  · intro h
    change Tendsto (fun i => hsNorm (matrixFrameLift (F i) (A.val i))) L (𝓝 0) at h
    change Tendsto (fun i => hsNorm (A.val i)) L (𝓝 0)
    have he : (fun i => hsNorm (A.val i)) =
        (fun i => Real.sqrt ((large i : ℝ) / dims i) * hsNorm (matrixFrameLift (F i) (A.val i))) :=
      funext fun i => matrixFrameLift_hsNorm_recover (hd i) (hN i) (F i) (hF i) (A.val i)
    rw [he]
    simpa using hratio.sqrt.mul h
  · exact matrixFrameSequenceLift_null dims large F hF hd hN L hratio A

include hN hratio in
theorem matrixFrameSequence_compression_error_null (A : BoundedMatrixSequence large) :
    A - matrixFrameSequenceLift dims large F hF (matrixFrameSequenceCompression dims large F hF A) ∈
      matrixNullIdeal large L := by
  obtain ⟨K, _, hK⟩ := BoundedMatrixSequence.bound large A
  change Tendsto (fun i => hsNorm (A.val i - matrixFrameLift (F i) ((F i)ᴴ * A.val i * F i))) L (𝓝 0)
  have he i : hsNorm (A.val i - matrixFrameLift (F i) ((F i)ᴴ * A.val i * F i)) ≤
      2 * hsNorm (1 - F i * (F i)ᴴ) * K := by
    have h := matrixFrame_compression_loss_opNorm (large i) (F i) (hF i) (A.val i)
    simp only [rectHSNorm_eq_hsNorm] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hK i) (mul_nonneg (by norm_num) (hsNorm_nonneg _)))
  exact squeeze_zero (fun i => hsNorm_nonneg _) he
    (by simpa using ((matrixFrame_complement_hsNorm_tendsto dims large F hF hN L hratio).const_mul 2).mul_const K)

include hN hratio in
theorem matrixFrameSequence_lift_compression_mk (A : BoundedMatrixSequence large) :
    matrixQuotientMk large L (matrixFrameSequenceLift dims large F hF
      (matrixFrameSequenceCompression dims large F hF A)) = matrixQuotientMk large L A := by
  symm
  exact (matrixQuotientMk_eq_iff large L _ _).mpr
    (matrixFrameSequence_compression_error_null dims large F hF hN L hratio A)

end ThomGame.Analysis
