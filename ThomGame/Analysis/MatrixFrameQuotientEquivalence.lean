module

public import ThomGame.Analysis.MatrixFrameQuotientHom

/-!
# The matrix quotient is unchanged by negligible frame stabilization

Zero extension is injective by the exact HS scaling identity. Every
target class has the original-dimensional compressed representative,
giving surjectivity and an explicit formula for the inverse.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix Filter
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} (dims large : ι → Nat)
    (F : (i : ι) → Matrix (Fin (large i)) (Fin (dims i)) ℂ)
    (hF : ∀ i, (F i)ᴴ * F i = 1) (hd : ∀ i, 0 < dims i) (hN : ∀ i, 0 < large i)
    (L : Filter ι) (hratio : Tendsto (fun i => (large i : ℝ) / dims i) L (𝓝 1))

theorem matrixFrameQuotientHom_injective :
    Function.Injective (matrixFrameQuotientHom dims large F hF hd hN L hratio) := by
  intro x y h
  obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims L x
  obtain ⟨B, rfl⟩ := matrixQuotientMk_surjective dims L y
  simp only [matrixFrameQuotientHom_mk] at h
  have hn := (Ideal.Quotient.eq).mp h
  rw [← map_sub] at hn
  exact Ideal.Quotient.eq.mpr ((matrixFrameSequenceLift_null_iff dims large F hF hd hN L hratio (A - B)).mp hn)

theorem matrixFrameQuotientHom_surjective :
    Function.Surjective (matrixFrameQuotientHom dims large F hF hd hN L hratio) := by
  intro y
  obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective large L y
  exact ⟨matrixQuotientMk dims L (matrixFrameSequenceCompression dims large F hF A),
    matrixFrameSequence_lift_compression_mk dims large F hF hN L hratio A⟩

noncomputable def matrixFrameQuotientEquiv :
    MatrixTracialQuotient dims L ≃⋆ₐ[ℂ] MatrixTracialQuotient large L :=
  StarAlgEquiv.ofBijective (matrixFrameQuotientHom dims large F hF hd hN L hratio)
    ⟨matrixFrameQuotientHom_injective dims large F hF hd hN L hratio,
      matrixFrameQuotientHom_surjective dims large F hF hd hN L hratio⟩

@[simp] theorem matrixFrameQuotientEquiv_mk (A : BoundedMatrixSequence dims) :
    matrixFrameQuotientEquiv dims large F hF hd hN L hratio (matrixQuotientMk dims L A) =
      matrixQuotientMk large L (matrixFrameSequenceLift dims large F hF A) := rfl

theorem matrixFrameQuotientEquiv_symm_mk (A : BoundedMatrixSequence large) :
    (matrixFrameQuotientEquiv dims large F hF hd hN L hratio).symm (matrixQuotientMk large L A) =
      matrixQuotientMk dims L (matrixFrameSequenceCompression dims large F hF A) := by
  apply (matrixFrameQuotientEquiv dims large F hF hd hN L hratio).injective
  change matrixFrameQuotientEquiv dims large F hF hd hN L hratio
      ((matrixFrameQuotientEquiv dims large F hF hd hN L hratio).symm (matrixQuotientMk large L A)) =
    matrixFrameQuotientEquiv dims large F hF hd hN L hratio
      (matrixQuotientMk dims L (matrixFrameSequenceCompression dims large F hF A))
  rw [StarAlgEquiv.apply_symm_apply, matrixFrameQuotientEquiv_mk]
  exact (matrixFrameSequence_lift_compression_mk dims large F hF hN L hratio A).symm

end ThomGame.Analysis
