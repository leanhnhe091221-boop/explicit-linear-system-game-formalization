module

public import ThomGame.Analysis.MatrixStableCornerTransport
public import ThomGame.Analysis.RectangularCompressionTraceLoss

/-!
# Distances between matrices in the common stable space

The intertwining error controls the difference of the transported support
corners. The remaining two errors are the actual support compressions.
All three terms use the same explicitly supplied HS denominator.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d m : Nat}

theorem matrixPartialIsometry_corner_difference (W : Matrix (Fin m) (Fin d) ℂ)
    (hW : IsStarProjection (Wᴴ * W)) (X : CMatrix d) (Y : CMatrix m) :
    (W * Wᴴ) * Y * (W * Wᴴ) - W * X * Wᴴ =
      (W * Wᴴ) * ((Y * W - W * X) * Wᴴ) := by
  have hw : (W * Wᴴ) * W = W := by
    rw [Matrix.mul_assoc]
    exact matrixPartialIsometry_mul_initial hW
  simp only [Matrix.sub_mul, Matrix.mul_sub]
  simp only [← Matrix.mul_assoc, hw]

theorem matrixPartialIsometry_corner_distance (r : Nat) (W : Matrix (Fin m) (Fin d) ℂ)
    (hW : IsStarProjection (Wᴴ * W)) (X : CMatrix d) (Y : CMatrix m) :
    rectHSNorm r ((W * Wᴴ) * Y * (W * Wᴴ) - W * X * Wᴴ) ≤
      rectHSNorm r (Y * W - W * X) := by
  rw [matrixPartialIsometry_corner_difference W hW X Y]
  have hq := matrixPartialIsometry_final_projection hW
  have hw : IsStarProjection (Wᴴᴴ * Wᴴ) := by
    simpa only [Matrix.conjTranspose_conjTranspose] using hq
  have ha := rectHSNorm_projection_mul_sq_le r hq ((Y * W - W * X) * Wᴴ)
  have hb := rectHSNorm_mul_sq_le_of_partialIsometry r (Y * W - W * X) hw
  exact (sq_le_sq₀ (rectHSNorm_nonneg r _) (rectHSNorm_nonneg r _)).mp (ha.trans hb)

theorem matrixFrames_intertwining_distance_bound {n : Nat} (r : Nat)
    (E : Matrix (Fin n) (Fin d) ℂ) (F : Matrix (Fin n) (Fin m) ℂ)
    (hE : Eᴴ * E = 1) (hF : Fᴴ * F = 1) (W : Matrix (Fin m) (Fin d) ℂ)
    (hW : IsStarProjection (Wᴴ * W)) (X : CMatrix d) (Y : CMatrix m)
    (hcorner : matrixFrameLift E ((Wᴴ * W) * X * (Wᴴ * W)) =
      matrixFrameLift F (W * X * Wᴴ)) :
    rectHSNorm r (matrixFrameLift E X - matrixFrameLift F Y) ≤
        rectHSNorm r (X - (Wᴴ * W) * X * (Wᴴ * W)) +
        rectHSNorm r (Y - (W * Wᴴ) * Y * (W * Wᴴ)) +
        rectHSNorm r (Y * W - W * X) := by
  let Xp := (Wᴴ * W) * X * (Wᴴ * W)
  let Yq := (W * Wᴴ) * Y * (W * Wᴴ)
  have hx : rectHSNorm r (matrixFrameLift E X - matrixFrameLift E Xp) =
      rectHSNorm r (X - Xp) := by rw [← matrixFrameLift_sub, matrixFrameLift_hsNorm r hE]
  have hy : rectHSNorm r (matrixFrameLift F Yq - matrixFrameLift F Y) =
      rectHSNorm r (Y - Yq) := by
    rw [← matrixFrameLift_sub, matrixFrameLift_hsNorm r hF, rectHSNorm_sub_comm]
  have hc : rectHSNorm r (matrixFrameLift E Xp - matrixFrameLift F Yq) ≤
      rectHSNorm r (Y * W - W * X) := by
    change rectHSNorm r (matrixFrameLift E ((Wᴴ * W) * X * (Wᴴ * W)) - matrixFrameLift F Yq) ≤ _
    rw [hcorner, ← matrixFrameLift_sub, matrixFrameLift_hsNorm r hF, rectHSNorm_sub_comm]
    exact matrixPartialIsometry_corner_distance r W hW X Y
  have he : matrixFrameLift E X - matrixFrameLift F Y =
      (matrixFrameLift E X - matrixFrameLift E Xp) +
      (matrixFrameLift F Yq - matrixFrameLift F Y) +
      (matrixFrameLift E Xp - matrixFrameLift F Yq) := by abel
  have ht := rectHSNorm_add_le r
    ((matrixFrameLift E X - matrixFrameLift E Xp) + (matrixFrameLift F Yq - matrixFrameLift F Y))
    (matrixFrameLift E Xp - matrixFrameLift F Yq)
  have ht' := rectHSNorm_add_le r (matrixFrameLift E X - matrixFrameLift E Xp)
    (matrixFrameLift F Yq - matrixFrameLift F Y)
  rw [← he] at ht
  rw [hx, hy] at ht'
  linarith

theorem matrixStableFrames_distance_bound (r : Nat) (W : Matrix (Fin m) (Fin d) ℂ)
    (hW : IsStarProjection (Wᴴ * W)) (X : CMatrix d) (Y : CMatrix m) :
    rectHSNorm r (matrixFrameLift (matrixStableSourceFrame W hW) X -
      matrixFrameLift (matrixStableTargetFrame W) Y) ≤
        rectHSNorm r (X - (Wᴴ * W) * X * (Wᴴ * W)) +
        rectHSNorm r (Y - (W * Wᴴ) * Y * (W * Wᴴ)) +
        rectHSNorm r (Y * W - W * X) :=
  matrixFrames_intertwining_distance_bound r _ _ (matrixStableSourceFrame_initial W hW)
    (matrixStableTargetFrame_initial W) W hW X Y (matrixStableFrames_source_corner W hW X)

end ThomGame.Analysis
