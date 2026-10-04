module

public import ThomGame.Analysis.MatrixPolarCompletion
public import ThomGame.Analysis.MatrixHilbertSchmidtLipschitz

/-!
# Unitary correction with a dimension independent Hilbert--Schmidt bound

Complete the polar factor on its missing supports. The scalar inequality
|sqrt(t)-1| ≤ |t-1| for t ≥ 0 controls its distance from the original
matrix by the Gram defect, with the original ambient normalization.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

theorem sqrt_sub_one_abs_le {t : ℝ} (ht : 0 ≤ t) :
    |Real.sqrt t - 1| ≤ |t - 1| := by
  have he : t - 1 = (Real.sqrt t - 1) * (Real.sqrt t + 1) := by
    nlinarith [Real.sq_sqrt ht]
  rw [he, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt t + 1)]
  nlinarith [abs_nonneg (Real.sqrt t - 1), Real.sqrt_nonneg t]

theorem matrixRectAbs_sub_one_le_gram {d : Nat} [NeZero d] (X : CMatrix d) :
    hsNorm (matrixRectAbs X - 1) ≤ hsNorm (Xᴴ * X - 1) := by
  have hA := Matrix.posSemidef_conjTranspose_mul_self X
  have hB : Matrix.IsHermitian (1 : CMatrix d) := Matrix.isHermitian_one
  have he (j : Fin d) : hB.eigenvalues j = 1 := by
    have hm := hB.eigenvalues_mem_spectrum_real j
    simpa only [CFC.spectrum_one_eq (R := ℝ), Set.mem_singleton_iff] using hm
  have hb := rectHSNorm_cfc_intertwiner_le_of_spectral_bound d hA.isHermitian hB
    Real.sqrt Real.sqrt (L := 1) zero_le_one (fun i j => by
      rw [he j, Real.sqrt_one, one_mul]
      exact sqrt_sub_one_abs_le (hA.eigenvalues_nonneg i)) (1 : CMatrix d)
  simpa only [Matrix.mul_one, Matrix.one_mul, one_mul, cfc_apply_one, Real.sqrt_one,
    map_one, matrixRectAbs, matrixSqrt_eq_real_cfc hA.nonneg, rectHSNorm_eq_hsNorm] using hb

theorem exists_matrixUnitary_close_of_gram {d : Nat} [NeZero d] (X : CMatrix d) :
    ∃ U : UnitaryMatrix d, hsNorm (X - U.val) ≤ hsNorm (Xᴴ * X - 1) := by
  obtain ⟨Z, hZi, hZf, hZX⟩ := exists_matrixPolar_completion
    (X := X) (IsStarProjection.one _) (IsStarProjection.one _) rfl (Matrix.mul_one X) (Matrix.one_mul X)
  let U : UnitaryMatrix d := ⟨Z, ⟨hZi, hZf⟩⟩
  have hX : X = U.val * matrixRectAbs X := by
    change X = Z * matrixRectAbs X
    rw [← hZX, ← Matrix.mul_assoc, hZf, Matrix.one_mul]
  refine ⟨U, ?_⟩
  calc
    hsNorm (X - U.val) = hsNorm (U.val * (matrixRectAbs X - 1)) := by
      congr 1
      rw [Matrix.mul_sub, Matrix.mul_one, ← hX]
    _ = hsNorm (matrixRectAbs X - 1) := hsNorm_unitary_mul U _
    _ ≤ hsNorm (Xᴴ * X - 1) := matrixRectAbs_sub_one_le_gram X

end ThomGame.Analysis
