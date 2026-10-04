module

public import ThomGame.Analysis.MatrixProjectionNearUnitary
public import ThomGame.Analysis.MatrixCanonicalCornerFrame
public import ThomGame.Analysis.MatrixFrameRectangularTransport

/-!
# Moving a retained frame into a specified corner

An ambient unitary close to one places the whole retained subspace in
the given corner. The resulting target frame has the same column count.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

theorem matrixFrame_unitary_initial {m k : Nat} (U : UnitaryMatrix m)
    (F : Matrix (Fin m) (Fin k) ℂ) (hF : Fᴴ * F = 1) :
    (U.val * F)ᴴ * (U.val * F) = 1 := by
  have hUi : U.valᴴ * U.val = 1 := U.prop.1
  rw [Matrix.conjTranspose_mul]
  calc
    _ = Fᴴ * (U.valᴴ * U.val) * F := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hUi, Matrix.mul_one, hF]

theorem exists_matrixFrame_move_to_corner_near {m d k : Nat} (r : Nat)
    (F : Matrix (Fin m) (Fin k) ℂ) (hF : Fᴴ * F = 1)
    (J : Matrix (Fin m) (Fin d) ℂ) (hJ : Jᴴ * J = 1) (hk : k ≤ d) :
    ∃ (U : UnitaryMatrix m) (G : Matrix (Fin d) (Fin k) ℂ),
      Gᴴ * G = 1 ∧ J * G = U.val * F ∧
      rectHSNorm r (U.val - 1) ≤ 4 * Real.sqrt (matrixTraceReal r (1 - F * Fᴴ)) := by
  have hP := matrixFrame_final_projection F hF
  have hQ := matrixFrame_final_projection J hJ
  obtain ⟨R, hR, hRQ, hr⟩ := exists_matrixSubprojection_rank hQ k
    (by rwa [matrixFrame_final_rank J hJ])
  obtain ⟨U, hU, hu⟩ := exists_matrixUnitary_projection_conjugacy_near r hP hR
    (by rw [matrixFrame_final_rank F hF, hr])
  let H := U.val * F
  have hHi : Hᴴ * H = 1 := matrixFrame_unitary_initial U F hF
  have hHf : H * Hᴴ = R := by
    rw [← hU]
    simp only [H, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hRH : R * H = H := by
    rw [← hHf, Matrix.mul_assoc, hHi, Matrix.mul_one]
  have hQH : (J * Jᴴ) * H = H := by
    calc
      _ = (J * Jᴴ) * (R * H) := by rw [hRH]
      _ = H := by rw [← Matrix.mul_assoc, (hR.le_iff_mul_eq_right hQ).mp hRQ, hRH]
  refine ⟨U, Jᴴ * H, ?_, matrixFrame_supported_lift J H hQH, hu⟩
  rw [matrixFrame_supported_gram J H hQH, hHi]

end ThomGame.Analysis
