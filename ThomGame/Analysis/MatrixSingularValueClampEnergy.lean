module

public import ThomGame.Analysis.MatrixSingularValueClamp
public import ThomGame.Analysis.MatrixIntertwiningEnergy

/-!
# Singular-value clipping contracts rectangular intertwining energy

The actual clipping map is equivariant under left and right unitaries
and is 1-Lipschitz in the normalized Hilbert--Schmidt norm. It follows
that clipping cannot increase the energy in ALT Proposition 3.5.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] in
theorem matrixRectClamp_gram_le_one (X : Matrix ι κ ℂ) :
    (matrixRectClamp X)ᴴ * matrixRectClamp X ≤ 1 := by
  rw [matrixRectClamp_gram, ← cfc_mul _ _ _
    ((matrixRectAbs X).finite_real_spectrum.continuousOn _)
    ((matrixRectAbs X).finite_real_spectrum.continuousOn _)]
  apply (cfc_le_one_iff _ _ ((matrixRectAbs X).finite_real_spectrum.continuousOn _)
    (matrixRectAbs_nonneg X).isSelfAdjoint).mpr
  intro t ht
  have hmin : 0 ≤ min t 1 := le_min
    (spectrum_nonneg_of_nonneg (matrixRectAbs_nonneg X) ht) zero_le_one
  calc
    _ ≤ 1 * min t 1 := mul_le_mul_of_nonneg_right (min_le_right _ _) hmin
    _ ≤ 1 := by simpa only [one_mul] using min_le_right t 1

theorem matrixRectClamp_unitary_left (V : Matrix.unitaryGroup ι ℂ) (X : Matrix ι κ ℂ) :
    matrixRectClamp (V.val * X) = V.val * matrixRectClamp X := by
  rw [matrixRectClamp, matrixRectAbs_unitary_left, Matrix.mul_assoc]
  rfl

omit [DecidableEq ι] in
theorem matrixRectClamp_unitary_right (U : Matrix.unitaryGroup κ ℂ) (X : Matrix ι κ ℂ) :
    matrixRectClamp (X * U.val) = matrixRectClamp X * U.val := by
  have he := matrix_cfc_intertwine (matrixRectAbs_isHermitian X)
    (matrixRectAbs_isHermitian (X * U.val)) (fun t : ℝ => (max t 1)⁻¹) U.val
    (matrixRectAbs_unitary_right_intertwine U X)
  rw [matrixRectClamp, Matrix.mul_assoc, ← he, ← Matrix.mul_assoc]
  rfl

theorem matrixRectClamp_two_unitaries (V : Matrix.unitaryGroup ι ℂ)
    (U : Matrix.unitaryGroup κ ℂ) (X : Matrix ι κ ℂ) :
    matrixRectClamp (V.val * X * U.val) = V.val * matrixRectClamp X * U.val := by
  rw [matrixRectClamp_unitary_right, matrixRectClamp_unitary_left]

theorem rectHSNorm_clamp_sub_le (r : Nat) (X Y : Matrix ι κ ℂ) :
    rectHSNorm r (matrixRectClamp X - matrixRectClamp Y) ≤ rectHSNorm r (X - Y) := by
  have he := rectHSNorm_cfc_sub_le_lipschitz r (matrixSelfAdjointDilation_isHermitian X)
    (matrixSelfAdjointDilation_isHermitian Y) (realNormClamp_lipschitz 1)
  simp only [NNReal.coe_one, one_mul, matrixSelfAdjointDilation_clamp,
    ← matrixSelfAdjointDilation_sub] at he
  have hs := mul_self_le_mul_self (rectHSNorm_nonneg _ _) he
  simp only [← pow_two, rectHSNorm_selfAdjointDilation_sq] at hs
  have hp := rectHSNorm_nonneg r (matrixRectClamp X - matrixRectClamp Y)
  have hq := rectHSNorm_nonneg r (X - Y)
  nlinarith

theorem rectHSNorm_clamp_intertwiner_le (r : Nat) (V : Matrix.unitaryGroup ι ℂ)
    (U : Matrix.unitaryGroup κ ℂ) (X : Matrix ι κ ℂ) :
    rectHSNorm r (V.val * matrixRectClamp X - matrixRectClamp X * U.val) ≤
      rectHSNorm r (V.val * X - X * U.val) := by
  rw [← matrixRectClamp_unitary_left, ← matrixRectClamp_unitary_right]
  exact rectHSNorm_clamp_sub_le r _ _

theorem matrixIntertwiningEnergy_clamp_le {h : Nat} (r : Nat)
    (U : Fin h → Matrix.unitaryGroup κ ℂ) (V : Fin h → Matrix.unitaryGroup ι ℂ)
    (X : Matrix ι κ ℂ) :
    matrixIntertwiningEnergy r U V (matrixRectClamp X) ≤ matrixIntertwiningEnergy r U V X := by
  apply mul_le_mul_of_nonneg_left _ (lazyMarkovWeight_nonneg h)
  apply Finset.sum_le_sum
  intro j _
  exact (sq_le_sq₀ (rectHSNorm_nonneg _ _) (rectHSNorm_nonneg _ _)).mpr
    (rectHSNorm_clamp_intertwiner_le r (V j) (U j) X)

end ThomGame.Analysis
