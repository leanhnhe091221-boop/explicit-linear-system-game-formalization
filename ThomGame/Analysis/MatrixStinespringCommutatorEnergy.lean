module

public import ThomGame.Analysis.MatrixRelativeStinespring
public import ThomGame.Analysis.MatrixExpectationProjectionGeometry
public import ThomGame.Analysis.MatrixCornerUnitary

/-!
# Exact commutator energy for the range of a trace expectation

The formula holds for every matrix, so the reverse-inclusion estimate
can be proved directly for contractions.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

theorem rectHSNorm_commutator_contraction_le {n : Nat} (r : Nat) (X Y Z : CMatrix n)
    (hX : matrixOpNorm X ≤ 1) (hXZ : X * Z = Z * X) :
    rectHSNorm r (X * Y - Y * X) ≤ 2 * rectHSNorm r (Y - Z) := by
  have he : X * Y - Y * X = X * (Y - Z) - (Y - Z) * X := by
    rw [mul_sub, sub_mul, hXZ]
    abel
  have hl : rectHSNorm r (X * (Y - Z)) ≤ rectHSNorm r (Y - Z) := by
    apply (rectHSNorm_mul_le_left r X (Y - Z)).trans
    simpa only [matrixOpNorm, one_mul] using
      mul_le_mul_of_nonneg_right hX (rectHSNorm_nonneg r (Y - Z))
  have hr : rectHSNorm r ((Y - Z) * X) ≤ rectHSNorm r (Y - Z) := by
    apply (rectHSNorm_mul_le_right r (Y - Z) X).trans
    simpa only [matrixOpNorm, mul_one] using
      mul_le_mul_of_nonneg_left hX (rectHSNorm_nonneg r (Y - Z))
  rw [he]
  exact (rectHSNorm_sub_le r _ _).trans (by linarith)

variable {d m : Nat} [NeZero d]

theorem matrixTraceProjection_pythagoras (A : StarSubalgebra ℂ (CMatrix d)) (X : CMatrix d) :
    hsNorm (X - matrixTraceProjection A X) ^ 2 =
      hsNorm X ^ 2 - hsNorm (matrixTraceProjection A X) ^ 2 := by
  have he : normalizedTrace (star X * matrixTraceProjection A X) =
      normalizedTrace (star (matrixTraceProjection A X) * matrixTraceProjection A X) := by
    rw [← matrixTraceProjection_trace A (star X * matrixTraceProjection A X),
      matrixTraceProjection_mul_right A _ _ (matrixTraceProjection_mem A X), matrixTraceProjection_star]
  rw [hsNorm_sub_sq, he, normalizedTrace_gram, Complex.ofReal_re]
  ring

theorem matrixStinespring_expectation_commutator_sq
    (A : StarSubalgebra ℂ (CMatrix d)) (ρ : CMatrix d →⋆ₐ[ℂ] CMatrix m)
    (V : Matrix (Fin m) (Fin d) ℂ) (hV : Vᴴ * V = 1)
    (hE : ∀ X, Vᴴ * ρ X * V = matrixTraceProjection A X) (X : CMatrix d) :
    rectHSNorm d (ρ X * (V * Vᴴ) - (V * Vᴴ) * ρ X) ^ 2 =
      2 * hsNorm (X - matrixTraceProjection A X) ^ 2 := by
  let p := V * Vᴴ
  have hp := matrixStinespring_range_projection V hV
  have hleft (Y : CMatrix d) : rectHSNorm d (ρ Y * p) ^ 2 = hsNorm Y ^ 2 := by
    calc
      _ = rectHSNorm d (ρ Y * V) ^ 2 := by
        rw [show ρ Y * p = (ρ Y * V) * Vᴴ by simp only [p, Matrix.mul_assoc],
          rectHSNorm_mul_frame_adjoint d hV]
      _ = matrixTraceReal d (Vᴴ * ρ (star Y * Y) * V) := by
        rw [← matrixTraceReal_gram]
        congr 1
        rw [map_mul, map_star]
        simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = hsNorm Y ^ 2 := by
        rw [hE, matrixTraceProjection_traceReal]
        exact matrixTraceReal_gram d Y
  have hright : rectHSNorm d (p * ρ X) ^ 2 = hsNorm X ^ 2 := by
    rw [← rectHSNorm_conjTranspose d (p * ρ X), Matrix.conjTranspose_mul,
      hp.isSelfAdjoint.isHermitian.eq]
    change rectHSNorm d (star (ρ X) * p) ^ 2 = _
    rw [← map_star, hleft, Matrix.star_eq_conjTranspose, hsNorm_conjTranspose]
  have hcross : matrixTraceReal d ((ρ X * p)ᴴ * (p * ρ X)) =
      hsNorm (matrixTraceProjection A X) ^ 2 := by
    calc
      _ = matrixTraceReal d (V * (Vᴴ * (ρ X)ᴴ * V * Vᴴ * ρ X)) := by
        congr 1
        simp only [p, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = matrixTraceReal d ((Vᴴ * (ρ X)ᴴ * V * Vᴴ * ρ X) * V) := matrixTraceReal_mul_comm d _ _
      _ = matrixTraceReal d ((Vᴴ * ρ X * V)ᴴ * (Vᴴ * ρ X * V)) := by
        congr 1
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = _ := by rw [matrixTraceReal_gram, hE]; rfl
  change rectHSNorm d (ρ X * p - p * ρ X) ^ 2 = _
  rw [rectHSNorm_sub_sq, matrixTraceReal_gram, matrixTraceReal_gram, hleft, hright, hcross,
    matrixTraceProjection_pythagoras]
  ring

end ThomGame.Analysis
