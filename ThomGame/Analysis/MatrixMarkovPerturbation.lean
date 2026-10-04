module

public import ThomGame.Analysis.MatrixMarkovPowers

/-!
# Perturbation bounds for actual Markov powers

The normalized operator-to-Hilbert--Schmidt perturbation of the n-th
power is at most n times the one-step perturbation. Unitary edits also
give a concrete one-step bound, independent of the matrix dimension.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {d h : Nat}

theorem matrixUnitaryConjugation_sub_le (U V : UnitaryMatrix d) (X : CMatrix d) :
    hsNorm (matrixUnitaryConjugation U X - matrixUnitaryConjugation V X) ≤
      2 * hsNorm (U.val - V.val) * matrixOpNorm X := by
  have he : matrixUnitaryConjugation U X - matrixUnitaryConjugation V X =
      (U.val - V.val) * X * (U⁻¹).val + V.val * (X * ((U⁻¹).val - (V⁻¹).val)) := by
    simp only [matrixUnitaryConjugation_apply, Matrix.UnitaryGroup.inv_val,
      sub_mul, mul_sub, mul_assoc]
    abel
  have hs : hsNorm ((U⁻¹).val - (V⁻¹).val) = hsNorm (U.val - V.val) := by
    rw [Matrix.UnitaryGroup.inv_val, Matrix.UnitaryGroup.inv_val, ← star_sub,
      Matrix.star_eq_conjTranspose, hsNorm_conjTranspose]
  rw [he]
  calc
    _ ≤ hsNorm ((U.val - V.val) * X * (U⁻¹).val) +
        hsNorm (V.val * (X * ((U⁻¹).val - (V⁻¹).val))) := hsNorm_add_le _ _
    _ = hsNorm ((U.val - V.val) * X) + hsNorm (X * ((U⁻¹).val - (V⁻¹).val)) := by
      rw [hsNorm_mul_unitary, hsNorm_unitary_mul]
    _ ≤ hsNorm (U.val - V.val) * matrixOpNorm X +
        matrixOpNorm X * hsNorm ((U⁻¹).val - (V⁻¹).val) :=
      add_le_add (hsNorm_mul_le_right _ _) (hsNorm_mul_le_left _ _)
    _ = _ := by rw [hs]; ring

theorem hsNorm_finset_sum_le {ι : Type*} (s : Finset ι) (F : ι → CMatrix d) :
    hsNorm (∑ i ∈ s, F i) ≤ ∑ i ∈ s, hsNorm (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, hsNorm_zero, le_refl]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (hsNorm_add_le _ _).trans (add_le_add_right ih _)

theorem matrixLazyMarkov_sub_hsNorm_le (U V : Fin h → UnitaryMatrix d) (X : CMatrix d) :
    hsNorm (matrixLazyMarkov U X - matrixLazyMarkov V X) ≤
      (4 * lazyMarkovWeight h * ∑ j, hsNorm ((U j).val - (V j).val)) * matrixOpNorm X := by
  have hinv (j : Fin h) : hsNorm (((U j)⁻¹).val - ((V j)⁻¹).val) = hsNorm ((U j).val - (V j).val) := by
    rw [Matrix.UnitaryGroup.inv_val, Matrix.UnitaryGroup.inv_val, ← star_sub,
      Matrix.star_eq_conjTranspose, hsNorm_conjTranspose]
  have hsum : hsNorm (∑ j, ((matrixUnitaryConjugation (U j) X - matrixUnitaryConjugation (V j) X) +
      (matrixUnitaryConjugation (U j)⁻¹ X - matrixUnitaryConjugation (V j)⁻¹ X))) ≤
      4 * (∑ j, hsNorm ((U j).val - (V j).val)) * matrixOpNorm X := by
    calc
      _ ≤ ∑ j, hsNorm ((matrixUnitaryConjugation (U j) X - matrixUnitaryConjugation (V j) X) +
          (matrixUnitaryConjugation (U j)⁻¹ X - matrixUnitaryConjugation (V j)⁻¹ X)) := hsNorm_finset_sum_le _ _
      _ ≤ ∑ j, 4 * hsNorm ((U j).val - (V j).val) * matrixOpNorm X := by
        apply Finset.sum_le_sum
        intro j _
        have hb := (hsNorm_add_le _ _).trans
          (add_le_add (matrixUnitaryConjugation_sub_le (U j) (V j) X)
            (matrixUnitaryConjugation_sub_le (U j)⁻¹ (V j)⁻¹ X))
        rw [hinv] at hb
        convert hb using 1; ring
      _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]
  have he : matrixLazyMarkov U X - matrixLazyMarkov V X = (lazyMarkovWeight h : ℂ) •
      ∑ j, ((matrixUnitaryConjugation (U j) X - matrixUnitaryConjugation (V j) X) +
        (matrixUnitaryConjugation (U j)⁻¹ X - matrixUnitaryConjugation (V j)⁻¹ X)) := by
    rw [matrixLazyMarkov_apply, matrixLazyMarkov_apply, add_sub_add_left_eq_sub, ← smul_sub,
      ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    abel
  rw [he, hsNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (lazyMarkovWeight_nonneg h)]
  calc
    _ ≤ lazyMarkovWeight h * (4 * (∑ j, hsNorm ((U j).val - (V j).val)) * matrixOpNorm X) :=
      mul_le_mul_of_nonneg_left hsum (lazyMarkovWeight_nonneg h)
    _ = _ := by ring

variable [NeZero d] [NeZero h]

theorem matrixLazyMarkov_pow_sub_hsNorm_le (U V : Fin h → UnitaryMatrix d) (ε : ℝ) (hε : 0 ≤ ε)
    (hstep : ∀ X, hsNorm (matrixLazyMarkov U X - matrixLazyMarkov V X) ≤ ε * matrixOpNorm X)
    (n : Nat) (X : CMatrix d) :
    hsNorm ((matrixLazyMarkov U ^ n) X - (matrixLazyMarkov V ^ n) X) ≤
      (n : ℝ) * ε * matrixOpNorm X := by
  induction n with
  | zero => simp only [pow_zero, Module.End.one_apply, sub_self, hsNorm_zero, Nat.cast_zero, zero_mul, le_refl]
  | succ n ih =>
      have he : (matrixLazyMarkov U ^ (n + 1)) X - (matrixLazyMarkov V ^ (n + 1)) X =
          matrixLazyMarkov U ((matrixLazyMarkov U ^ n) X - (matrixLazyMarkov V ^ n) X) +
          (matrixLazyMarkov U ((matrixLazyMarkov V ^ n) X) - matrixLazyMarkov V ((matrixLazyMarkov V ^ n) X)) := by
        simp only [pow_succ', Module.End.mul_apply, map_sub]
        abel
      rw [he]
      calc
        _ ≤ hsNorm (matrixLazyMarkov U ((matrixLazyMarkov U ^ n) X - (matrixLazyMarkov V ^ n) X)) +
            hsNorm (matrixLazyMarkov U ((matrixLazyMarkov V ^ n) X) - matrixLazyMarkov V ((matrixLazyMarkov V ^ n) X)) :=
          hsNorm_add_le _ _
        _ ≤ (n : ℝ) * ε * matrixOpNorm X + ε * matrixOpNorm ((matrixLazyMarkov V ^ n) X) :=
          add_le_add ((matrixLazyMarkov_hsNorm_le U _).trans ih) (hstep _)
        _ ≤ (n : ℝ) * ε * matrixOpNorm X + ε * matrixOpNorm X :=
          add_le_add_right (mul_le_mul_of_nonneg_left (matrixLazyMarkov_pow_matrixOpNorm_le V n X) hε) _
        _ = _ := by rw [Nat.cast_add, Nat.cast_one]; ring

theorem matrixLazyMarkov_pow_sub_mixedNorm_le (U V : Fin h → UnitaryMatrix d) (n : Nat) :
    matrixMixedNorm (matrixLazyMarkov U ^ n - matrixLazyMarkov V ^ n) ≤
      (n : ℝ) * matrixMixedNorm (matrixLazyMarkov U - matrixLazyMarkov V) := by
  apply matrixMixedNorm_le _ _ (mul_nonneg (Nat.cast_nonneg _) (matrixMixedNorm_nonneg _))
  intro X
  exact matrixLazyMarkov_pow_sub_hsNorm_le U V _ (matrixMixedNorm_nonneg _)
    (hsNorm_apply_le_matrixMixedNorm (matrixLazyMarkov U - matrixLazyMarkov V)) n X

end ThomGame.Analysis
