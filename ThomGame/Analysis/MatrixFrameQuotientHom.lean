module

public import ThomGame.Analysis.MatrixFrameSequenceLimits

/-!
# The genuine unital star homomorphism induced by frame stabilization

The sequence map is zero extension. Its missing unit lies in the proved
null ideal, so its descended map is a unital complex star homomorphism.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix Filter
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} (dims large : ι → Nat)
    (F : (i : ι) → Matrix (Fin (large i)) (Fin (dims i)) ℂ)
    (hF : ∀ i, (F i)ᴴ * F i = 1) (hd : ∀ i, 0 < dims i) (hN : ∀ i, 0 < large i)
    (L : Filter ι) (hratio : Tendsto (fun i => (large i : ℝ) / dims i) L (𝓝 1))

include hN hratio in
theorem matrixFrameSequenceLift_one_mk :
    matrixQuotientMk large L (matrixFrameSequenceLift dims large F hF 1) = 1 := by
  have h := matrixFrameSequence_lift_compression_mk dims large F hF hN L hratio 1
  rwa [matrixFrameSequenceCompression_one, (matrixQuotientMk large L).map_one] at h

noncomputable def matrixFrameQuotientHom :
    MatrixTracialQuotient dims L →⋆ₐ[ℂ] MatrixTracialQuotient large L where
  toFun := Quotient.lift (fun A => matrixQuotientMk large L (matrixFrameSequenceLift dims large F hF A)) (by
    intro A B h
    apply Ideal.Quotient.eq.mpr
    rw [← map_sub]
    exact matrixFrameSequenceLift_null dims large F hF hd hN L hratio (A - B)
      ((Submodule.quotientRel_def _).mp h))
  map_zero' := by
    change matrixQuotientMk large L (matrixFrameSequenceLift dims large F hF 0) = 0
    rw [map_zero, map_zero]
  map_one' := matrixFrameSequenceLift_one_mk dims large F hF hN L hratio
  map_add' x y := by
    obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims L x
    obtain ⟨B, rfl⟩ := matrixQuotientMk_surjective dims L y
    change matrixQuotientMk large L (matrixFrameSequenceLift dims large F hF (A + B)) = _
    rw [map_add, map_add]
    rfl
  map_mul' x y := by
    obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims L x
    obtain ⟨B, rfl⟩ := matrixQuotientMk_surjective dims L y
    change matrixQuotientMk large L (matrixFrameSequenceLift dims large F hF (A * B)) = _
    rw [matrixFrameSequenceLift_mul, map_mul]
    rfl
  commutes' c := by
    change matrixQuotientMk large L (matrixFrameSequenceLift dims large F hF
      (algebraMap ℂ (BoundedMatrixSequence dims) c)) = algebraMap ℂ (MatrixTracialQuotient large L) c
    rw [Algebra.algebraMap_eq_smul_one, map_smul]
    change (matrixQuotientStarAlgHom large L) (c • matrixFrameSequenceLift dims large F hF 1) = _
    rw [map_smul]
    change c • matrixQuotientMk large L (matrixFrameSequenceLift dims large F hF 1) = _
    rw [matrixFrameSequenceLift_one_mk dims large F hF hN L hratio, Algebra.algebraMap_eq_smul_one]
  map_star' x := by
    obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims L x
    change matrixQuotientMk large L (matrixFrameSequenceLift dims large F hF (star A)) = _
    rw [matrixFrameSequenceLift_star, ← matrixQuotientMk_star]
    rfl

@[simp] theorem matrixFrameQuotientHom_mk (A : BoundedMatrixSequence dims) :
    matrixFrameQuotientHom dims large F hF hd hN L hratio (matrixQuotientMk dims L A) =
      matrixQuotientMk large L (matrixFrameSequenceLift dims large F hF A) := rfl

end ThomGame.Analysis
