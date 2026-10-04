module

public import ThomGame.Analysis.MatrixProjectionIsometry
public import ThomGame.Analysis.MatrixPinchingRankCorrection

/-!
# Completing the actual polar factor between prescribed equal-rank supports

The two missing supports have the same rank. An actual partial
isometry between them is added orthogonally to the polar factor.
The completed map still pairs with X as the positive absolute value.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] in
theorem matrixRectPolar_initial_le {X : Matrix ι κ ℂ} {P : Matrix κ κ ℂ}
    (hP : IsStarProjection P) (hXP : X * P = X) :
    (matrixRectPolar X)ᴴ * matrixRectPolar X ≤ P := by
  rw [matrixRectPolar_initial]
  apply ((matrixRealSupport_isStarProjection _).le_iff_mul_eq_left hP).mpr
  have he := matrix_absSupport_mul_eq_zero (X := X) (Z := 1 - P) (by
    rw [Matrix.mul_sub, Matrix.mul_one, hXP, sub_self])
  rw [Matrix.mul_sub, Matrix.mul_one] at he
  exact (sub_eq_zero.mp he).symm

theorem matrixRectPolar_final_le {X : Matrix ι κ ℂ} {Q : Matrix ι ι ℂ}
    (hQ : IsStarProjection Q) (hQX : Q * X = X) :
    matrixRectPolar X * (matrixRectPolar X)ᴴ ≤ Q := by
  have he := matrixRectPolar_initial_le hQ (X := Xᴴ) (by
    simpa only [Matrix.conjTranspose_mul, hQ.isSelfAdjoint.isHermitian.eq] using congrArg Matrix.conjTranspose hQX)
  simpa only [matrixRectPolar_conjTranspose, Matrix.conjTranspose_conjTranspose] using he

omit [DecidableEq ι] in
theorem matrixRectPolar_adjoint_mul (X : Matrix ι κ ℂ) :
    (matrixRectPolar X)ᴴ * X = matrixRectAbs X := by
  calc
    _ = (matrixRectPolar X)ᴴ * (matrixRectPolar X * matrixRectAbs X) := by rw [matrixRectPolar_mul_abs]
    _ = _ := by rw [← Matrix.mul_assoc, matrixRectPolar_initial, matrixRealSupport_mul (matrixRectAbs_isHermitian X)]

theorem exists_matrixPolar_completion {X : Matrix ι κ ℂ} {P : Matrix κ κ ℂ} {Q : Matrix ι ι ℂ}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (hrank : P.rank = Q.rank)
    (hXP : X * P = X) (hQX : Q * X = X) :
    ∃ Z : Matrix ι κ ℂ, Zᴴ * Z = P ∧ Z * Zᴴ = Q ∧ Zᴴ * X = matrixRectAbs X := by
  let V := matrixRectPolar X
  let I := Vᴴ * V
  let F := V * Vᴴ
  have hI : IsStarProjection I := matrixRectPolar_initial_projection X
  have hF : IsStarProjection F := matrixRectPolar_final_projection X
  have hIP : I ≤ P := matrixRectPolar_initial_le hP hXP
  have hFQ : F ≤ Q := matrixRectPolar_final_le hQ hQX
  have hPi : IsStarProjection (P - I) := (hI.le_iff_sub hP).mp hIP
  have hQf : IsStarProjection (Q - F) := (hF.le_iff_sub hQ).mp hFQ
  have hIF : I.rank = F.rank := by
    dsimp only [I, F]
    rw [Matrix.rank_conjTranspose_mul_self, Matrix.rank_self_mul_conjTranspose]
  have hr : (P - I).rank = (Q - F).rank := by
    have hi := matrixProjection_rank_sub_add hP hI hIP
    have hf := matrixProjection_rank_sub_add hQ hF hFQ
    omega
  obtain ⟨W, hWi, hWf⟩ := exists_matrixPartialIsometry_of_rank_eq hPi hQf hr
  have hW : IsStarProjection (Wᴴ * W) := hWi.symm ▸ hPi
  have hWright : W * (P - I) = W := by rw [← hWi]; exact matrixPartialIsometry_mul_initial hW
  have hWleft : (Q - F) * W = W := by
    rw [← hWf, Matrix.mul_assoc, hWi, hWright]
  have hVright : V * I = V := by
    dsimp only [I, V]
    rw [← Matrix.mul_assoc, matrixRectPolar_partial_isometry]
  have hVleft : F * V = V := matrixRectPolar_partial_isometry X
  have hVP : V * P = V := by
    calc
      _ = (V * I) * P := by rw [hVright]
      _ = V := by rw [Matrix.mul_assoc, (hI.le_iff_mul_eq_left hP).mp hIP, hVright]
  have hQV : Q * V = V := by
    calc
      _ = Q * (F * V) := by rw [hVleft]
      _ = V := by rw [← Matrix.mul_assoc, (hF.le_iff_mul_eq_right hQ).mp hFQ, hVleft]
  have hVWi : V * Wᴴ = 0 := by
    have he : (P - I) * Wᴴ = Wᴴ := by
      simpa only [Matrix.conjTranspose_mul, hPi.isSelfAdjoint.isHermitian.eq] using congrArg Matrix.conjTranspose hWright
    calc
      _ = V * ((P - I) * Wᴴ) := by rw [he]
      _ = 0 := by rw [← Matrix.mul_assoc, Matrix.mul_sub, hVP, hVright, sub_self, Matrix.zero_mul]
  have hVWf : Vᴴ * W = 0 := by
    have hq : Vᴴ * Q = Vᴴ := by
      simpa only [Matrix.conjTranspose_mul, hQ.isSelfAdjoint.isHermitian.eq] using congrArg Matrix.conjTranspose hQV
    have hf : Vᴴ * F = Vᴴ := by
      simpa only [Matrix.conjTranspose_mul, hF.isSelfAdjoint.isHermitian.eq] using congrArg Matrix.conjTranspose hVleft
    calc
      _ = Vᴴ * ((Q - F) * W) := by rw [hWleft]
      _ = 0 := by rw [← Matrix.mul_assoc, Matrix.mul_sub, hq, hf, sub_self, Matrix.zero_mul]
  have hWVi : W * Vᴴ = 0 := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero] using congrArg Matrix.conjTranspose hVWi
  have hWVf : Wᴴ * V = 0 := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero] using congrArg Matrix.conjTranspose hVWf
  have hWX : Wᴴ * X = 0 := by
    calc
      _ = Wᴴ * (V * matrixRectAbs X) := by rw [matrixRectPolar_mul_abs]
      _ = 0 := by rw [← Matrix.mul_assoc, hWVf, Matrix.zero_mul]
  refine ⟨V + W, ?_, ?_, ?_⟩
  · simp only [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, hVWf, hWVf, hWi]
    change I + 0 + (0 + (P - I)) = P
    abel
  · simp only [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, hVWi, hWVi, hWf]
    change F + 0 + (0 + (Q - F)) = Q
    abel
  · rw [Matrix.conjTranspose_add, Matrix.add_mul, hWX, add_zero]
    exact matrixRectPolar_adjoint_mul X

end ThomGame.Analysis
