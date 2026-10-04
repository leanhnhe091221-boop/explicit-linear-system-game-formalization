module

public import ThomGame.Analysis.MatrixStinespring
public import ThomGame.Analysis.MatrixExpectationCompletelyPositive
public import ThomGame.Analysis.RectangularNormalizedTrace
public import ThomGame.Analysis.MatrixNearInclusion
public import ThomGame.Analysis.MatrixChannelEnergy

/-!
# Exact and approximate intertwining in a matrix Stinespring dilation

Gram identities give the multiplicative-domain relation and the exact
trace-preserving expectation error. All rectangular norms retain d as
their denominator, independently of the dimension of the dilation.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat} {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem matrixStinespring_defect_gram
    (ρ : CMatrix d →⋆ₐ[ℂ] Matrix κ κ ℂ) (V : Matrix κ (Fin d) ℂ)
    (hV : Vᴴ * V = 1) (X Y : CMatrix d) :
    (ρ X * V - V * Y)ᴴ * (ρ X * V - V * Y) =
      Vᴴ * ρ (star X * X) * V - Vᴴ * ρ (star X) * V * Y -
        star Y * (Vᴴ * ρ X * V) + star Y * Y := by
  have h₁ : (Vᴴ * (ρ X)ᴴ) * (ρ X * V) = Vᴴ * ρ (star X * X) * V := by
    rw [map_mul, map_star]
    simp only [Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
  have h₂ : (Vᴴ * (ρ X)ᴴ) * (V * Y) = Vᴴ * ρ (star X) * V * Y := by
    rw [map_star]
    simp only [Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
  have h₃ : (Yᴴ * Vᴴ) * (ρ X * V) = star Y * (Vᴴ * ρ X * V) := by
    simp only [Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
  have h₄ : (Yᴴ * Vᴴ) * (V * Y) = star Y * Y := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ V Y, hV, Matrix.one_mul]
    rfl
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, h₁, h₂, h₃, h₄]
  abel

theorem matrixStinespring_intertwines_of_gram
    (ρ : CMatrix d →⋆ₐ[ℂ] Matrix κ κ ℂ) (V : Matrix κ (Fin d) ℂ)
    (hV : Vᴴ * V = 1) (X Y : CMatrix d)
    (hX : Vᴴ * ρ X * V = Y)
    (hXX : Vᴴ * ρ (star X * X) * V = star Y * Y) :
    ρ X * V = V * Y := by
  have hs : Vᴴ * ρ (star X) * V = star Y := by
    have he := congrArg Matrix.conjTranspose hX
    rw [map_star]
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.star_eq_conjTranspose, Matrix.mul_assoc] using he
  apply sub_eq_zero.mp
  apply Matrix.conjTranspose_mul_self_eq_zero.mp
  rw [matrixStinespring_defect_gram ρ V hV, hXX, hs, hX]
  abel

variable [NeZero d]

theorem matrixStinespring_expectation_intertwines
    (A : StarSubalgebra ℂ (CMatrix d))
    (ρ : CMatrix d →⋆ₐ[ℂ] Matrix κ κ ℂ) (V : Matrix κ (Fin d) ℂ)
    (hV : Vᴴ * V = 1)
    (hE : ∀ X, Vᴴ * ρ X * V = matrixTraceProjection A X)
    (X : CMatrix d) (hX : X ∈ A) : ρ X * V = V * X := by
  apply matrixStinespring_intertwines_of_gram ρ V hV X X
  · rw [hE, matrixTraceProjection_eq_self A X hX]
  · rw [hE, matrixTraceProjection_eq_self A _ (A.mul_mem (A.star_mem' hX) hX)]

theorem matrixStinespring_expectation_defect_sq
    (A : StarSubalgebra ℂ (CMatrix d))
    (ρ : CMatrix d →⋆ₐ[ℂ] Matrix κ κ ℂ) (V : Matrix κ (Fin d) ℂ)
    (hV : Vᴴ * V = 1)
    (hE : ∀ X, Vᴴ * ρ X * V = matrixTraceProjection A X)
    (X : CMatrix d) :
    rectHSNorm d (ρ X * V - V * X) ^ 2 = 2 * hsNorm (X - matrixTraceProjection A X) ^ 2 := by
  have hp := matrixTraceProjection_pairing A X (matrixTraceProjection A X)
    (matrixTraceProjection_mem A X)
  have hps : normalizedTrace (star (matrixTraceProjection A X) * X) =
      normalizedTrace (star X * matrixTraceProjection A X) := by
    rw [← matrixTraceProjection_star]
    rw [← matrixTraceProjection_trace A (star X * matrixTraceProjection A X),
      matrixTraceProjection_mul_right A _ _ (matrixTraceProjection_mem A X),
      matrixTraceProjection_star]
    exact hp.symm
  have he := congrArg (fun Z : CMatrix d => (normalizedTrace Z).re)
    (matrixStinespring_defect_gram ρ V hV X X)
  have hg : (normalizedTrace ((ρ X * V - V * X)ᴴ * (ρ X * V - V * X))).re =
      rectHSNorm d (ρ X * V - V * X) ^ 2 := by
    simpa only [normalizedTrace_re, matrixTraceReal] using
      matrixTraceReal_gram d (ρ X * V - V * X)
  rw [hg] at he
  simp only [hE, normalizedTrace_sub, normalizedTrace_add, matrixTraceProjection_trace,
    Complex.sub_re, Complex.add_re, matrixTraceProjection_star, normalizedTrace_gram,
    Complex.ofReal_re, hps] at he
  rw [← hps, ← hp, normalizedTrace_gram, Complex.ofReal_re] at he
  rw [hsNorm_sub_sq]
  rw [← hps, ← hp, normalizedTrace_gram, Complex.ofReal_re]
  linarith

theorem matrixStinespring_expectation_nearInclusion_bound
    (A B : StarSubalgebra ℂ (CMatrix d)) {ε : ℝ} (hε : 0 ≤ ε)
    (hBA : MatrixNearInclusion B A ε)
    (ρ : CMatrix d →⋆ₐ[ℂ] Matrix κ κ ℂ) (V : Matrix κ (Fin d) ℂ)
    (hV : Vᴴ * V = 1)
    (hE : ∀ X, Vᴴ * ρ X * V = matrixTraceProjection A X)
    (X : CMatrix d) (hX : X ∈ B) (hbound : matrixOpNorm X ≤ 1) :
    rectHSNorm d (ρ X * V - V * X) ≤ Real.sqrt 2 * ε := by
  obtain ⟨Y, hYA, hY⟩ := hBA X hX hbound
  have hb := (matrixTraceProjection_bestApproximation A X Y hYA).trans hY
  have he := matrixStinespring_expectation_defect_sq A ρ V hV hE X
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : 0 ≤ Real.sqrt 2 * ε := mul_nonneg (Real.sqrt_nonneg _) hε
  apply (sq_le_sq₀ (rectHSNorm_nonneg d _) hp).mp
  rw [he, mul_pow, hs]
  exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ (hsNorm_nonneg _) hε).mpr hb) (by norm_num)

end ThomGame.Analysis
