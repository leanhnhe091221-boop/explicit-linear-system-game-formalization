module

public import ThomGame.Analysis.MatrixArakiYamagami
public import ThomGame.Analysis.MatrixMarkovPoincare
public import ThomGame.Analysis.CStarNormLift

/-!
# Functional calculus preserves small commutator energy

A scalar L-Lipschitz function multiplies the actual matrix boundary
energy by at most L squared. In particular, clipping self-adjoint
matrices and taking their positive parts do not increase this energy.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators NNReal Matrix.Norms.L2Operator

variable {d h : Nat} {A : CMatrix d}

theorem hsNorm_cfc_commutator_le (hA : Matrix.IsHermitian A) (f : ℝ → ℝ)
    {L : ℝ} (hL : 0 ≤ L) (hf : ∀ a b, |f a - f b| ≤ L * |a - b|) (X : CMatrix d) :
    hsNorm (X * cfc f A - cfc f A * X) ≤ L * hsNorm (X * A - A * X) := by
  rw [hsNorm_sub_comm (X * cfc f A), hsNorm_sub_comm (X * A)]
  exact rectHSNorm_cfc_intertwiner_le d hA hA f hL hf X

theorem matrixCoordinateEnergy_cfc_le (U : Fin h → UnitaryMatrix d)
    (hA : Matrix.IsHermitian A) (f : ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ a b, |f a - f b| ≤ L * |a - b|) :
    matrixCoordinateEnergy U (cfc f A) ≤ L ^ 2 * matrixCoordinateEnergy U A := by
  unfold matrixCoordinateEnergy
  rw [mul_left_comm (L ^ 2)]
  apply mul_le_mul_of_nonneg_left _ (lazyMarkovWeight_nonneg h)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have he := mul_self_le_mul_self (hsNorm_nonneg _)
    (hsNorm_cfc_commutator_le hA f hL hf (U j).val)
  simpa only [← pow_two, mul_pow] using he

theorem matrixCoordinateEnergy_cfc_le_lipschitz (U : Fin h → UnitaryMatrix d)
    (hA : Matrix.IsHermitian A) {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    matrixCoordinateEnergy U (cfc f A) ≤ (L : ℝ) ^ 2 * matrixCoordinateEnergy U A := by
  apply matrixCoordinateEnergy_cfc_le U hA f L.coe_nonneg
  intro a b
  simpa only [Real.dist_eq] using hf.dist_le_mul a b

theorem realNormClamp_lipschitz (K : ℝ) : LipschitzWith 1 (realNormClamp K) :=
  (LipschitzWith.id.const_min K).const_max (-K)

theorem hsNorm_normClamp_sub_le (K : ℝ) {B : CMatrix d}
    (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B) :
    hsNorm (cstarNormClamp K A - cstarNormClamp K B) ≤ hsNorm (A - B) := by
  simpa only [NNReal.coe_one, one_mul, cstarNormClamp, rectHSNorm_eq_hsNorm] using
    rectHSNorm_cfc_sub_le_lipschitz d hA hB (realNormClamp_lipschitz K)

theorem matrixCoordinateEnergy_normClamp_le (U : Fin h → UnitaryMatrix d)
    (K : ℝ) (hA : Matrix.IsHermitian A) :
    matrixCoordinateEnergy U (cstarNormClamp K A) ≤ matrixCoordinateEnergy U A := by
  simpa only [NNReal.coe_one, one_pow, one_mul, cstarNormClamp] using
    matrixCoordinateEnergy_cfc_le_lipschitz U hA (realNormClamp_lipschitz K)

theorem hsNorm_cfc_positivePart_sub_le {B : CMatrix d}
    (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B) :
    hsNorm (cfc (fun t : ℝ => max t 0) A - cfc (fun t : ℝ => max t 0) B) ≤
      hsNorm (A - B) := by
  simpa only [NNReal.coe_one, one_mul, id_eq, rectHSNorm_eq_hsNorm] using
    rectHSNorm_cfc_sub_le_lipschitz d hA hB (LipschitzWith.id.max_const (0 : ℝ))

theorem matrixCoordinateEnergy_cfc_positivePart_le (U : Fin h → UnitaryMatrix d)
    (hA : Matrix.IsHermitian A) :
    matrixCoordinateEnergy U (cfc (fun t : ℝ => max t 0) A) ≤ matrixCoordinateEnergy U A := by
  simpa only [NNReal.coe_one, one_pow, one_mul, id_eq] using
    matrixCoordinateEnergy_cfc_le_lipschitz U hA (LipschitzWith.id.max_const (0 : ℝ))

theorem matrixCoordinateEnergy_cfc_abs_le (U : Fin h → UnitaryMatrix d)
    (hA : Matrix.IsHermitian A) :
    matrixCoordinateEnergy U (cfc (abs : ℝ → ℝ) A) ≤ matrixCoordinateEnergy U A := by
  simpa only [one_pow, one_mul] using matrixCoordinateEnergy_cfc_le U hA abs
    (L := 1) zero_le_one (fun a b => by simpa using abs_abs_sub_abs_le_abs_sub a b)

end ThomGame.Analysis
