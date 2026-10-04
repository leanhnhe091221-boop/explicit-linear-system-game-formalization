module

public import ThomGame.Analysis.MatrixBoundedScaleTransport
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Order of bounded scales for commuting positive matrices

The regularizing matrix need not be central in either algebra. Pairwise
commutation with the two scales is sufficient, with no conditioning bound.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} {T U M : CMatrix d}

theorem matrixCommute_nonsing_inv_right (h : Commute T M) (hM : IsUnit M) :
    Commute T M⁻¹ :=
  (matrixNonsingular_inverse_intertwines M M T hM hM h.symm.eq).symm

theorem matrixCommute_posDef_mul (hT : T.PosDef) (hM : M.PosDef) (h : Commute T M) :
    (T * M).PosDef :=
  (Matrix.nonneg_iff_posSemidef.mp (Commute.mul_nonneg hT.posSemidef.nonneg
    hM.posSemidef.nonneg h)).posDef_iff_isUnit.mpr (hT.isUnit.mul hM.isUnit)

theorem matrixPosDef_inverse_antitone (hT : T.PosDef) (hU : U.PosDef) (hTU : T ≤ U) :
    U⁻¹ ≤ T⁻¹ := by
  have h := CStarAlgebra.inv_le_inv (a := hT.isUnit.unit) (b := hU.isUnit.unit)
    (by simpa only [IsUnit.unit_spec] using hT.posSemidef.nonneg)
    (by simpa only [IsUnit.unit_spec] using hTU)
  simpa only [Matrix.coe_units_inv, IsUnit.unit_spec] using h

theorem matrixBoundedScale_one_sub (h : IsUnit (T + M)) :
    1 - matrixBoundedScale T M = M * (T + M)⁻¹ := by
  have hi := Matrix.mul_nonsing_inv (T + M) ((Matrix.isUnit_iff_isUnit_det _).mp h)
  rw [Matrix.add_mul] at hi
  rw [matrixBoundedScale]
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hi.symm)

theorem matrixBoundedScale_posDef (hT : T.PosDef) (hM : M.PosDef) (hTM : Commute T M) :
    (matrixBoundedScale T M).PosDef := by
  exact matrixCommute_posDef_mul hT (hT.add hM).inv
    (matrixCommute_nonsing_inv_right ((Commute.refl T).add_right hTM) (hT.add hM).isUnit)

theorem matrixBoundedScale_one_sub_posDef (hT : T.PosDef) (hM : M.PosDef)
    (hTM : Commute T M) : (1 - matrixBoundedScale T M).PosDef := by
  rw [matrixBoundedScale_one_sub (hT.add hM).isUnit]
  exact matrixCommute_posDef_mul hM (hT.add hM).inv
    (matrixCommute_nonsing_inv_right (hTM.symm.add_right (Commute.refl M)) (hT.add hM).isUnit)

theorem matrixBoundedScale_mono (hT : T.PosDef) (hU : U.PosDef) (hM : M.PosDef)
    (hTM : Commute T M) (hUM : Commute U M) (hTU : T ≤ U) :
    matrixBoundedScale T M ≤ matrixBoundedScale U M := by
  have hi := matrixPosDef_inverse_antitone (hT.add hM) (hU.add hM) (add_le_add hTU le_rfl)
  have hcT := matrixCommute_nonsing_inv_right
    (hTM.symm.add_right (Commute.refl M)) (hT.add hM).isUnit
  have hcU := matrixCommute_nonsing_inv_right
    (hUM.symm.add_right (Commute.refl M)) (hU.add hM).isUnit
  have hp := Commute.mul_nonneg hM.posSemidef.nonneg (sub_nonneg.mpr hi) (hcT.sub_right hcU)
  have he : matrixBoundedScale U M - matrixBoundedScale T M =
      M * ((T + M)⁻¹ - (U + M)⁻¹) := by
    rw [mul_sub, ← matrixBoundedScale_one_sub (hT.add hM).isUnit,
      ← matrixBoundedScale_one_sub (hU.add hM).isUnit]
    abel
  exact sub_nonneg.mp (he ▸ hp)

theorem matrixBoundedScale_norm_le_one (hT : T.PosDef) (hM : M.PosDef)
    (hTM : Commute T M) : matrixOpNorm (matrixBoundedScale T M) ≤ 1 :=
  (CStarAlgebra.norm_le_one_iff_of_nonneg _
    (matrixBoundedScale_posDef hT hM hTM).posSemidef.nonneg).mpr
      (sub_nonneg.mp (matrixBoundedScale_one_sub_posDef hT hM hTM).posSemidef.nonneg)

end ThomGame.Analysis
