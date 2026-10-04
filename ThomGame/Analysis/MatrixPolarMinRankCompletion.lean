module

public import ThomGame.Analysis.MatrixProjectionIntermediateRank
public import ThomGame.Analysis.MatrixPolarCompletion
public import ThomGame.Analysis.MatrixProjectionPieceEnergy

/-!
# Polar completion to the smaller corner rank

Both actual polar supports are extended inside their prescribed
corners to min(rank P, rank Q), then the polar map is completed between
them. This handles unequal corner ranks and nontrivial kernels.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat}

theorem exists_matrixPolar_min_rank_completion (P Q X : CMatrix d)
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (hl : P * X = X) (hr : X * Q = X) :
    ∃ U : CMatrix d, P * U = U ∧ U * Q = U ∧
      IsStarProjection (star U * U) ∧ IsStarProjection (U * star U) ∧
      star U * U ≤ Q ∧ U * star U ≤ P ∧
      (star U * U).rank = min P.rank Q.rank ∧ (U * star U).rank = min P.rank Q.rank ∧
      star U * X = matrixRectAbs X ∧ matrixOpNorm U ≤ 1 := by
  let I := (matrixRectPolar X)ᴴ * matrixRectPolar X
  let J := matrixRectPolar X * (matrixRectPolar X)ᴴ
  have hI : IsStarProjection I := matrixRectPolar_initial_projection X
  have hJ : IsStarProjection J := matrixRectPolar_final_projection X
  have hIQ : I ≤ Q := matrixRectPolar_initial_le hQ hr
  have hJP : J ≤ P := matrixRectPolar_final_le hP hl
  have hIr : I.rank = X.rank := by
    dsimp only [I]
    rw [Matrix.rank_conjTranspose_mul_self, matrixRectPolar_rank]
  have hJr : J.rank = X.rank := by
    dsimp only [J]
    rw [Matrix.rank_self_mul_conjTranspose, matrixRectPolar_rank]
  have hXP : X.rank ≤ P.rank := by
    rw [← hl]
    exact Matrix.rank_mul_le_left P X
  have hXQ : X.rank ≤ Q.rank := by
    rw [← hr]
    exact Matrix.rank_mul_le_right X Q
  have hIt : I.rank ≤ min P.rank Q.rank := by rw [hIr]; exact le_min hXP hXQ
  have hJt : J.rank ≤ min P.rank Q.rank := by rw [hJr]; exact le_min hXP hXQ
  obtain ⟨I', hI', hII', hI'Q, hI'r⟩ := exists_matrixProjection_intermediate_rank hI hQ hIQ
    (min P.rank Q.rank) hIt (min_le_right _ _)
  obtain ⟨J', hJ', hJJ', hJ'P, hJ'r⟩ := exists_matrixProjection_intermediate_rank hJ hP hJP
    (min P.rank Q.rank) hJt (min_le_left _ _)
  have hXI : X * I = X := by
    dsimp only [I]
    rw [matrixRectPolar_initial, matrix_mul_absSupport]
  have hJX : J * X = X := matrixRectPolar_final_mul X
  have hXI' : X * I' = X := by
    calc
      _ = (X * I) * I' := by rw [hXI]
      _ = X := by rw [mul_assoc, (hI.le_iff_mul_eq_left hI').mp hII', hXI]
  have hJ'X : J' * X = X := by
    calc
      _ = J' * (J * X) := by rw [hJX]
      _ = X := by rw [← mul_assoc, (hJ.le_iff_mul_eq_right hJ').mp hJJ', hJX]
  obtain ⟨U, hUi, hUf, hUX⟩ := exists_matrixPolar_completion hI' hJ' (hI'r.trans hJ'r.symm) hXI' hJ'X
  have hU : IsStarProjection (Uᴴ * U) := hUi.symm ▸ hI'
  have hUI' : U * I' = U := by rw [← hUi]; exact matrixPartialIsometry_mul_initial hU
  have hJ'U : J' * U = U := by rw [← hUf, mul_assoc, hUi, hUI']
  refine ⟨U, ?_, ?_, hUi.symm ▸ hI', hUf.symm ▸ hJ', hUi.symm ▸ hI'Q, hUf.symm ▸ hJ'P,
    hUi.symm ▸ hI'r, hUf.symm ▸ hJ'r, hUX, matrixPartialIsometry_norm_le_one hU⟩
  · calc
      _ = P * (J' * U) := by rw [hJ'U]
      _ = U := by rw [← mul_assoc, (hJ'.le_iff_mul_eq_right hP).mp hJ'P, hJ'U]
  · calc
      _ = (U * I') * Q := by rw [hUI']
      _ = U := by rw [mul_assoc, (hI'.le_iff_mul_eq_left hQ).mp hI'Q, hUI']

end ThomGame.Analysis
