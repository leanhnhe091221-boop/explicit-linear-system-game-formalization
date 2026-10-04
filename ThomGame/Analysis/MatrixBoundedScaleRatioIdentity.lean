module

public import ThomGame.Analysis.MatrixCommutingBoundedScale

/-!
# A polynomial identity for the inverse scale ratio

Clearing actual invertible matrix denominators avoids divisions by
bounded scales near the endpoints of their spectra.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} {T U M : CMatrix d}

theorem matrixBoundedScale_mul_sum (h : IsUnit (T + M)) :
    matrixBoundedScale T M * (T + M) = T := by
  rw [matrixBoundedScale, mul_assoc, Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).mp h), mul_one]

theorem matrixBoundedScale_one_sub_mul_sum (h : IsUnit (T + M)) :
    (1 - matrixBoundedScale T M) * (T + M) = M := by
  rw [sub_mul, one_mul, matrixBoundedScale_mul_sum h]
  abel

theorem matrixBoundedScale_ratio_defect_identity
    (hT : T.PosDef) (hU : U.PosDef) (hM : M.PosDef)
    (hTU : Commute T U) (hTM : Commute T M) (hUM : Commute U M) :
    (1 - U⁻¹ * T) * matrixBoundedScale U M * (1 - matrixBoundedScale T M) =
      matrixBoundedScale U M - matrixBoundedScale T M := by
  apply ((hT.add hM).isUnit.mul (hU.add hM).isUnit).mul_right_cancel
  have hswap : Commute (T + M) (U + M) :=
    (hTU.add_right hTM).add_left (hUM.symm.add_right (Commute.refl M))
  have hratio : (1 - U⁻¹ * T) * U = U - T := by
    rw [sub_mul, one_mul, mul_assoc, hTU.eq, ← mul_assoc,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hU.isUnit), one_mul]
  calc
    _ = (1 - U⁻¹ * T) * matrixBoundedScale U M * M * (U + M) := by
      rw [← mul_assoc _ (T + M) (U + M),
        mul_assoc ((1 - U⁻¹ * T) * matrixBoundedScale U M),
        matrixBoundedScale_one_sub_mul_sum (hT.add hM).isUnit]
    _ = (1 - U⁻¹ * T) * (matrixBoundedScale U M * (U + M)) * M := by
      simp only [mul_assoc, (hUM.symm.add_right (Commute.refl M)).eq]
    _ = (U - T) * M := by rw [matrixBoundedScale_mul_sum (hU.add hM).isUnit, hratio]
    _ = U * (T + M) - T * (U + M) := by noncomm_ring [hTU.symm.eq]
    _ = (matrixBoundedScale U M - matrixBoundedScale T M) * ((T + M) * (U + M)) := by
      rw [sub_mul, ← mul_assoc (matrixBoundedScale T M),
        matrixBoundedScale_mul_sum (hT.add hM).isUnit, hswap.eq,
        ← mul_assoc (matrixBoundedScale U M), matrixBoundedScale_mul_sum (hU.add hM).isUnit]

end ThomGame.Analysis
