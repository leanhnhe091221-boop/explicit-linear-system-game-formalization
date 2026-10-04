module

public import ThomGame.Analysis.MatrixFrameCompression

/-!
# Star representations on reducing matrix ranges

Compression is multiplicative only on the specified reducing subalgebra.
The same frame transports exact intertwining and commutation.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix

variable {d m k : Nat}

theorem matrixFrame_reducing_intertwines {F : Matrix (Fin m) (Fin k) ℂ}
    (hF : Fᴴ * F = 1) (X : CMatrix m) (hX : (F * Fᴴ) * X = X * (F * Fᴴ)) :
    X * F = F * (Fᴴ * X * F) := by
  calc
    X * F = X * (F * Fᴴ) * F := by simp only [Matrix.mul_assoc, hF, Matrix.mul_one]
    _ = (F * Fᴴ) * X * F := by rw [hX]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem matrixFrame_reducing_adjoint_intertwines {F : Matrix (Fin m) (Fin k) ℂ}
    (hF : Fᴴ * F = 1) (X : CMatrix m) (hX : (F * Fᴴ) * X = X * (F * Fᴴ)) :
    Fᴴ * X = (Fᴴ * X * F) * Fᴴ := by
  calc
    Fᴴ * X = Fᴴ * (F * Fᴴ) * X := by rw [← Matrix.mul_assoc Fᴴ F Fᴴ, hF, Matrix.one_mul]
    _ = Fᴴ * (X * (F * Fᴴ)) := by rw [Matrix.mul_assoc, hX]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem matrixFrame_reducing_mul {F : Matrix (Fin m) (Fin k) ℂ}
    (hF : Fᴴ * F = 1) (X Y : CMatrix m) (hY : (F * Fᴴ) * Y = Y * (F * Fᴴ)) :
    Fᴴ * (X * Y) * F = (Fᴴ * X * F) * (Fᴴ * Y * F) := by
  calc
    _ = Fᴴ * X * (Y * F) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [matrixFrame_reducing_intertwines hF Y hY]; simp only [Matrix.mul_assoc]

noncomputable def matrixReducingRepresentation (B : StarSubalgebra ℂ (CMatrix d))
    (ρ : CMatrix d →⋆ₐ[ℂ] CMatrix m) (F : Matrix (Fin m) (Fin k) ℂ)
    (hF : Fᴴ * F = 1) (hcomm : ∀ X ∈ B, (F * Fᴴ) * ρ X = ρ X * (F * Fᴴ)) :
    B →⋆ₐ[ℂ] CMatrix k where
  toFun X := Fᴴ * ρ X * F
  map_one' := by simp only [OneMemClass.coe_one, map_one, Matrix.mul_one, hF]
  map_mul' X Y := by
    change Fᴴ * ρ ((X : CMatrix d) * (Y : CMatrix d)) * F = _
    rw [map_mul]
    exact matrixFrame_reducing_mul hF (ρ X) (ρ Y) (hcomm Y Y.property)
  map_zero' := by simp
  map_add' X Y := by
    change Fᴴ * ρ ((X : CMatrix d) + (Y : CMatrix d)) * F = _
    rw [map_add, Matrix.mul_add, Matrix.add_mul]
  commutes' c := by
    change Fᴴ * ρ (algebraMap ℂ (CMatrix d) c) * F = algebraMap ℂ (CMatrix k) c
    rw [Algebra.algebraMap_eq_smul_one, map_smul, map_one, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hF, Algebra.algebraMap_eq_smul_one]
  map_star' X := by
    change Fᴴ * ρ (star (X : CMatrix d)) * F = (Fᴴ * ρ X * F)ᴴ
    rw [map_star]
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

theorem matrixReducingRepresentation_apply (B : StarSubalgebra ℂ (CMatrix d))
    (ρ : CMatrix d →⋆ₐ[ℂ] CMatrix m) (F : Matrix (Fin m) (Fin k) ℂ)
    (hF : Fᴴ * F = 1) (hcomm : ∀ X ∈ B, (F * Fᴴ) * ρ X = ρ X * (F * Fᴴ)) (X : B) :
    matrixReducingRepresentation B ρ F hF hcomm X = Fᴴ * ρ X * F := rfl

theorem matrixFrame_compressions_commute {F : Matrix (Fin m) (Fin k) ℂ}
    (hF : Fᴴ * F = 1) (X Y : CMatrix m)
    (hX : (F * Fᴴ) * X = X * (F * Fᴴ)) (hY : (F * Fᴴ) * Y = Y * (F * Fᴴ))
    (hXY : X * Y = Y * X) :
    (Fᴴ * X * F) * (Fᴴ * Y * F) = (Fᴴ * Y * F) * (Fᴴ * X * F) := by
  rw [← matrixFrame_reducing_mul hF X Y hY, ← matrixFrame_reducing_mul hF Y X hX, hXY]

end ThomGame.Analysis
