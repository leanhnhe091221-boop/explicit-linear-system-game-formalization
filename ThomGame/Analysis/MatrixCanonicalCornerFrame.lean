module

public import ThomGame.Analysis.MatrixFrameStabilizationBounds

/-!
# The specified standard coordinate corner

The frame includes the first d coordinates in m coordinates. It depends
only on the two dimensions and gives the canonical ambient identification.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

def matrixCanonicalCornerFrame {d m : Nat} (hd : d ≤ m) :
    Matrix (Fin m) (Fin d) ℂ :=
  (1 : CMatrix m).submatrix id (Fin.castLE hd)

theorem matrixCanonicalCornerFrame_initial {d m : Nat} (hd : d ≤ m) :
    (matrixCanonicalCornerFrame hd)ᴴ * matrixCanonicalCornerFrame hd = 1 := by
  rw [matrixCanonicalCornerFrame, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one]
  change (1 : CMatrix m).submatrix (Fin.castLE hd) (Equiv.refl (Fin m)) *
    (1 : CMatrix m).submatrix (Equiv.refl (Fin m)) (Fin.castLE hd) = _
  rw [Matrix.submatrix_mul_equiv, Matrix.one_mul]
  exact Matrix.submatrix_one _ (Fin.castLE_injective hd)

theorem matrixFrame_final_rank {m k : Nat} (F : Matrix (Fin m) (Fin k) ℂ)
    (hF : Fᴴ * F = 1) : (F * Fᴴ).rank = k := by
  rw [Matrix.rank_self_mul_conjTranspose, ← Matrix.rank_conjTranspose_mul_self F,
    hF, Matrix.rank_one, Fintype.card_fin]

theorem matrixCanonicalCornerFrame_rank {d m : Nat} (hd : d ≤ m) :
    (matrixCanonicalCornerFrame hd * (matrixCanonicalCornerFrame hd)ᴴ).rank = d :=
  matrixFrame_final_rank _ (matrixCanonicalCornerFrame_initial hd)

end ThomGame.Analysis
