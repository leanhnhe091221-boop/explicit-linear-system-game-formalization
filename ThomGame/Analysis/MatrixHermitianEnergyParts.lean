module

public import ThomGame.Analysis.MatrixCheegerSelfAdjoint

/-!
# Exact Hilbert--Schmidt and energy splitting into Hermitian parts

Conjugation preserves Hermitian matrices. The real and imaginary
parts of its displacement satisfy an exact Pythagorean identity.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {d h : Nat}

theorem normalizedTrace_selfAdjoint_real {A : CMatrix d} (hA : IsSelfAdjoint A) :
    ((normalizedTrace A).re : ℂ) = normalizedTrace A := by
  have ht : star (normalizedTrace A) = normalizedTrace A := by rw [← normalizedTrace_star, hA.star_eq]
  have hi := congrArg Complex.im ht
  simp only [Complex.star_def, Complex.conj_im] at hi
  apply Complex.ext
  · simp
  · simp only [Complex.ofReal_im]
    linarith only [hi]

theorem matrix_selfAdjoint_center {A : CMatrix d} (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (A - normalizedTrace A • 1) := by
  change star (A - normalizedTrace A • (1 : CMatrix d)) = _
  rw [star_sub, star_smul, star_one, hA.star_eq, ← normalizedTrace_star, hA.star_eq]

variable [NeZero d]

theorem hsNorm_selfAdjoint_add_I_smul_sq {A B : CMatrix d}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    hsNorm (A + Complex.I • B) ^ 2 = hsNorm A ^ 2 + hsNorm B ^ 2 := by
  have hs : star (A + Complex.I • B) = A - Complex.I • B := by
    simp only [star_add, star_smul, hA.star_eq, hB.star_eq, Complex.star_def,
      Complex.conj_I, neg_smul, sub_eq_add_neg]
  have hn : hsNorm (A - Complex.I • B) = hsNorm (A + Complex.I • B) := by
    rw [← hs]
    exact hsNorm_conjTranspose _
  have hh := parallelogram_law_with_norm ℂ (finiteMatrixHilbertEquiv d A)
    (finiteMatrixHilbertEquiv d (Complex.I • B))
  simp only [← map_add, ← map_sub, finiteMatrixHilbert_norm, hn, hsNorm_smul, Complex.norm_I, one_mul] at hh
  linarith only [hh]

theorem matrixCoordinateEnergy_selfAdjoint_add_I_smul (U : Fin h → UnitaryMatrix d)
    {A B : CMatrix d} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    matrixCoordinateEnergy U (A + Complex.I • B) = matrixCoordinateEnergy U A + matrixCoordinateEnergy U B := by
  have hj (j : Fin h) : hsNorm ((U j).val * (A + Complex.I • B) - (A + Complex.I • B) * (U j).val) ^ 2 =
      hsNorm ((U j).val * A - A * (U j).val) ^ 2 + hsNorm ((U j).val * B - B * (U j).val) ^ 2 := by
    simp only [← matrixUnitaryConjugation_sub_hsNorm]
    have he : matrixUnitaryConjugation (U j) (A + Complex.I • B) - (A + Complex.I • B) =
        (matrixUnitaryConjugation (U j) A - A) + Complex.I • (matrixUnitaryConjugation (U j) B - B) := by
      rw [map_add, map_smul, smul_sub]
      abel
    rw [he]
    apply hsNorm_selfAdjoint_add_I_smul_sq
    · exact (hA.map (Unitary.conjStarAlgAut ℂ (CMatrix d) (U j))).sub hA
    · exact (hB.map (Unitary.conjStarAlgAut ℂ (CMatrix d) (U j))).sub hB
  simp only [matrixCoordinateEnergy]
  simp_rw [hj]
  rw [Finset.sum_add_distrib, mul_add]

theorem hsNorm_center_selfAdjoint_add_I_smul_sq {A B : CMatrix d}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    hsNorm ((A + Complex.I • B) - normalizedTrace (A + Complex.I • B) • 1) ^ 2 =
      hsNorm (A - normalizedTrace A • 1) ^ 2 + hsNorm (B - normalizedTrace B • 1) ^ 2 := by
  have he : (A + Complex.I • B) - normalizedTrace (A + Complex.I • B) • 1 =
      (A - normalizedTrace A • 1) + Complex.I • (B - normalizedTrace B • 1) := by
    rw [normalizedTrace_add, normalizedTrace_smul, add_smul, smul_sub, mul_smul]
    abel
  rw [he]
  exact hsNorm_selfAdjoint_add_I_smul_sq (matrix_selfAdjoint_center hA) (matrix_selfAdjoint_center hB)

end ThomGame.Analysis
