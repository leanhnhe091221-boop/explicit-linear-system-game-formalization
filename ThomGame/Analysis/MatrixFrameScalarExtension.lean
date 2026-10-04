module

public import ThomGame.Analysis.MatrixStableCornerTransport

/-!
# Extending an embedded algebra by scalars on its added corner

The actual star representation of A × C has image F A F* + C(1-FF*).
Compression recovers the original A component, including when the added
corner has dimension zero.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d n : Nat}

theorem matrixFrame_complement_adjoint (F : Matrix (Fin n) (Fin d) ℂ) (hF : Fᴴ * F = 1) :
    Fᴴ * (1 - F * Fᴴ) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hF, Matrix.one_mul, sub_self]

theorem matrixFrame_complement (F : Matrix (Fin n) (Fin d) ℂ) (hF : Fᴴ * F = 1) :
    (1 - F * Fᴴ) * F = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hF, Matrix.mul_one, sub_self]

theorem matrixFrameLift_mul_complement (F : Matrix (Fin n) (Fin d) ℂ) (hF : Fᴴ * F = 1)
    (X : CMatrix d) : matrixFrameLift F X * (1 - F * Fᴴ) = 0 := by
  rw [matrixFrameLift, Matrix.mul_assoc, matrixFrame_complement_adjoint F hF, Matrix.mul_zero]

theorem matrixFrameLift_complement_mul (F : Matrix (Fin n) (Fin d) ℂ) (hF : Fᴴ * F = 1)
    (X : CMatrix d) : (1 - F * Fᴴ) * matrixFrameLift F X = 0 := by
  rw [matrixFrameLift, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    matrixFrame_complement F hF, Matrix.zero_mul, Matrix.zero_mul]

noncomputable def matrixFrameScalarRepresentation (A : StarSubalgebra ℂ (CMatrix d))
    (F : Matrix (Fin n) (Fin d) ℂ) (hF : Fᴴ * F = 1) : A × ℂ →⋆ₐ[ℂ] CMatrix n where
  toFun X := matrixFrameLift F (X.1 : CMatrix d) + X.2 • (1 - F * Fᴴ)
  map_one' := by
    change matrixFrameLift F 1 + (1 : ℂ) • (1 - F * Fᴴ) = 1
    rw [matrixFrameLift_one, one_smul, add_sub_cancel]
  map_zero' := by simp [matrixFrameLift]
  map_add' X Y := by
    change matrixFrameLift F ((X.1 : CMatrix d) + (Y.1 : CMatrix d)) +
      (X.2 + Y.2) • (1 - F * Fᴴ) = _
    rw [matrixFrameLift_add, add_smul]
    abel
  map_mul' X Y := by
    change matrixFrameLift F ((X.1 : CMatrix d) * (Y.1 : CMatrix d)) +
      (X.2 * Y.2) • (1 - F * Fᴴ) = _
    symm
    simp only [add_mul, mul_add, Matrix.mul_smul, Matrix.smul_mul,
      matrixFrameLift_mul hF, matrixFrameLift_mul_complement F hF,
      matrixFrameLift_complement_mul F hF, smul_zero, add_zero, zero_add, smul_smul,
      (matrixFrame_final_projection F hF).one_sub.isIdempotentElem.eq]
    rw [mul_comm Y.2 X.2]
  commutes' c := by
    change matrixFrameLift F (algebraMap ℂ (CMatrix d) c) + c • (1 - F * Fᴴ) =
      algebraMap ℂ (CMatrix n) c
    rw [Algebra.algebraMap_eq_smul_one, matrixFrameLift_smul, matrixFrameLift_one,
      ← smul_add, add_sub_cancel, Algebra.algebraMap_eq_smul_one]
  map_star' X := by
    change matrixFrameLift F (star (X.1 : CMatrix d)) + star X.2 • (1 - F * Fᴴ) =
      star (matrixFrameLift F (X.1 : CMatrix d) + X.2 • (1 - F * Fᴴ))
    rw [star_add, star_smul, (matrixFrame_final_projection F hF).one_sub.isSelfAdjoint.star_eq]
    exact congrArg (fun Z : CMatrix n => Z + star X.2 • (1 - F * Fᴴ))
      (matrixFrameLift_star F (X.1 : CMatrix d)).symm

noncomputable def matrixFrameScalarAlgebra (A : StarSubalgebra ℂ (CMatrix d))
    (F : Matrix (Fin n) (Fin d) ℂ) (hF : Fᴴ * F = 1) : StarSubalgebra ℂ (CMatrix n) :=
  (matrixFrameScalarRepresentation A F hF).range

theorem mem_matrixFrameScalarAlgebra (A : StarSubalgebra ℂ (CMatrix d))
    (F : Matrix (Fin n) (Fin d) ℂ) (hF : Fᴴ * F = 1) (Z : CMatrix n) :
    Z ∈ matrixFrameScalarAlgebra A F hF ↔
      ∃ X ∈ A, ∃ c : ℂ, matrixFrameLift F X + c • (1 - F * Fᴴ) = Z := by
  constructor
  · rintro ⟨⟨X, c⟩, he⟩
    exact ⟨X, X.property, c, he⟩
  · rintro ⟨X, hX, c, he⟩
    exact ⟨(⟨X, hX⟩, c), he⟩

theorem matrixFrameScalarAlgebra_lift_mem (A : StarSubalgebra ℂ (CMatrix d))
    (F : Matrix (Fin n) (Fin d) ℂ) (hF : Fᴴ * F = 1) (X : CMatrix d) (hX : X ∈ A) :
    matrixFrameLift F X ∈ matrixFrameScalarAlgebra A F hF := by
  exact (mem_matrixFrameScalarAlgebra A F hF _).mpr ⟨X, hX, 0, by simp⟩

theorem matrixFrameScalarAlgebra_compression_mem (A : StarSubalgebra ℂ (CMatrix d))
    (F : Matrix (Fin n) (Fin d) ℂ) (hF : Fᴴ * F = 1) (Z : CMatrix n)
    (hZ : Z ∈ matrixFrameScalarAlgebra A F hF) : Fᴴ * Z * F ∈ A := by
  obtain ⟨X, hX, c, rfl⟩ := (mem_matrixFrameScalarAlgebra A F hF Z).mp hZ
  have he : Fᴴ * matrixFrameLift F X * F = X := by
    simp only [matrixFrameLift, Matrix.mul_assoc]
    rw [hF, Matrix.mul_one, ← Matrix.mul_assoc, hF, Matrix.one_mul]
  rw [Matrix.mul_add, Matrix.add_mul, he, Matrix.mul_smul,
    matrixFrame_complement_adjoint F hF, smul_zero, Matrix.zero_mul, add_zero]
  exact hX

theorem matrixFrameScalarAlgebra_mono (A B : StarSubalgebra ℂ (CMatrix d))
    (F : Matrix (Fin n) (Fin d) ℂ) (hF : Fᴴ * F = 1) (hAB : A ≤ B) :
    matrixFrameScalarAlgebra A F hF ≤ matrixFrameScalarAlgebra B F hF := by
  intro Z hZ
  obtain ⟨X, hX, c, he⟩ := (mem_matrixFrameScalarAlgebra A F hF Z).mp hZ
  exact (mem_matrixFrameScalarAlgebra B F hF Z).mpr ⟨X, hAB hX, c, he⟩

end ThomGame.Analysis
