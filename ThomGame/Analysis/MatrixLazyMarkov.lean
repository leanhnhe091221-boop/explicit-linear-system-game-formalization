module

public import ThomGame.Analysis.MatrixUnitaryConjugation
public import ThomGame.Analysis.LazyHilbertAverage
public import Mathlib.Analysis.Matrix.Order

/-!
# The actual lazy Markov map of a unitary matrix tuple

The matrix formula is ALT's one-half identity plus the symmetric
conjugation average. Its trace Hilbert operator is the previously proved
lazy average. In particular its energy is the normalized sum of squared
commutators, and its fixed matrices are precisely the common commutant.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {d h : Nat} (U : Fin h → UnitaryMatrix d)

noncomputable def matrixLazyMarkov : CMatrix d →ₗ[ℂ] CMatrix d :=
  ((1 / 2 : ℝ) : ℂ) • LinearMap.id +
    (lazyMarkovWeight h : ℂ) • ∑ j, (matrixUnitaryConjugation (U j) + matrixUnitaryConjugation (U j)⁻¹)

@[simp] theorem matrixLazyMarkov_apply (X : CMatrix d) :
    matrixLazyMarkov U X = ((1 / 2 : ℝ) : ℂ) • X + (lazyMarkovWeight h : ℂ) •
      ∑ j, (matrixUnitaryConjugation (U j) X + matrixUnitaryConjugation (U j)⁻¹ X) := by
  simp only [matrixLazyMarkov, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.sum_apply]

theorem matrixLazyMarkov_star (X : CMatrix d) :
    matrixLazyMarkov U (star X) = star (matrixLazyMarkov U X) := by
  simp only [matrixLazyMarkov_apply, matrixUnitaryConjugation_star, star_add, star_smul,
    star_sum, Complex.star_def, Complex.conj_ofReal]

theorem matrixLazyMarkov_nonneg (X : CMatrix d) (hX : 0 ≤ X) : 0 ≤ matrixLazyMarkov U X := by
  rw [matrixLazyMarkov_apply]
  apply add_nonneg
  · exact smul_nonneg (by exact_mod_cast (show (0 : ℝ) ≤ 1 / 2 by norm_num)) hX
  · apply smul_nonneg
    · exact_mod_cast lazyMarkovWeight_nonneg h
    · apply Finset.sum_nonneg
      intro j _
      exact add_nonneg (star_right_conjugate_nonneg hX (U j).val)
        (star_right_conjugate_nonneg hX ((U j)⁻¹).val)

variable [NeZero h]

theorem matrixLazyMarkov_matrixOpNorm_le (X : CMatrix d) :
    matrixOpNorm (matrixLazyMarkov U X) ≤ matrixOpNorm X := by
  have hsum : matrixOpNorm (∑ j, (matrixUnitaryConjugation (U j) X +
      matrixUnitaryConjugation (U j)⁻¹ X)) ≤ (h : ℝ) * (2 * matrixOpNorm X) := by
    calc
      _ ≤ ∑ j, matrixOpNorm (matrixUnitaryConjugation (U j) X + matrixUnitaryConjugation (U j)⁻¹ X) :=
        norm_sum_le _ _
      _ ≤ ∑ _j : Fin h, 2 * matrixOpNorm X := by
        apply Finset.sum_le_sum
        intro j _
        simpa only [matrixUnitaryConjugation_matrixOpNorm, two_mul] using
          matrixOpNorm_add_le (matrixUnitaryConjugation (U j) X) (matrixUnitaryConjugation (U j)⁻¹ X)
      _ = _ := by simp
  rw [matrixLazyMarkov_apply]
  calc
    _ ≤ matrixOpNorm (((1 / 2 : ℝ) : ℂ) • X) + matrixOpNorm ((lazyMarkovWeight h : ℂ) •
        ∑ j, (matrixUnitaryConjugation (U j) X + matrixUnitaryConjugation (U j)⁻¹ X)) := matrixOpNorm_add_le _ _
    _ = 1 / 2 * matrixOpNorm X + lazyMarkovWeight h * matrixOpNorm
        (∑ j, (matrixUnitaryConjugation (U j) X + matrixUnitaryConjugation (U j)⁻¹ X)) := by
      rw [matrixOpNorm_smul, matrixOpNorm_smul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
        abs_of_nonneg (lazyMarkovWeight_nonneg h)]
    _ ≤ 1 / 2 * matrixOpNorm X + lazyMarkovWeight h * ((h : ℝ) * (2 * matrixOpNorm X)) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hsum (lazyMarkovWeight_nonneg h)) _
    _ = matrixOpNorm X := by rw [← mul_assoc, lazyMarkovWeight_mul_card]; ring

variable [NeZero d]

omit [NeZero h] in
theorem matrixLazyMarkov_hilbert (X : CMatrix d) :
    finiteMatrixHilbertEquiv d (matrixLazyMarkov U X) =
      lazyHilbertAverage (fun j => matrixConjugationHilbertEquiv (U j)) (finiteMatrixHilbertEquiv d X) := by
  simp only [matrixLazyMarkov_apply, lazyHilbertAverage_apply, map_add, map_smul, map_sum,
    matrixConjugationHilbertEquiv_apply, matrixConjugationHilbertEquiv_symm_apply,
    matrixConjugationHilbert_embedding]

theorem matrixLazyMarkov_hsNorm_le (X : CMatrix d) : hsNorm (matrixLazyMarkov U X) ≤ hsNorm X := by
  simpa only [← matrixLazyMarkov_hilbert, finiteMatrixHilbert_norm] using
    lazyHilbertAverage_norm_apply_le (fun j => matrixConjugationHilbertEquiv (U j)) (finiteMatrixHilbertEquiv d X)

omit [NeZero h] in
theorem matrixLazyMarkov_pairing (X Y : CMatrix d) :
    normalizedTrace (star (matrixLazyMarkov U X) * Y) = normalizedTrace (star X * matrixLazyMarkov U Y) := by
  have hs := lazyHilbertAverage_symmetric (fun j => matrixConjugationHilbertEquiv (U j))
    (finiteMatrixHilbertEquiv d X) (finiteMatrixHilbertEquiv d Y)
  change inner ℂ (lazyHilbertAverage (fun j => matrixConjugationHilbertEquiv (U j))
      (finiteMatrixHilbertEquiv d X)) (finiteMatrixHilbertEquiv d Y) =
    inner ℂ (finiteMatrixHilbertEquiv d X) (lazyHilbertAverage (fun j => matrixConjugationHilbertEquiv (U j))
      (finiteMatrixHilbertEquiv d Y)) at hs
  simpa only [← matrixLazyMarkov_hilbert, finiteMatrixHilbert_inner] using hs

theorem matrixLazyMarkov_energy (X : CMatrix d) :
    (normalizedTrace (star X * (X - matrixLazyMarkov U X))).re =
      lazyMarkovWeight h * ∑ j, hsNorm ((U j).val * X - X * (U j).val) ^ 2 := by
  have he := lazyHilbertAverage_energy (fun j => matrixConjugationHilbertEquiv (U j)) (finiteMatrixHilbertEquiv d X)
  simpa only [← matrixLazyMarkov_hilbert, ← map_sub, finiteMatrixHilbert_inner,
    matrixConjugationHilbertEquiv_apply, matrixConjugationHilbert_sub_norm] using he

theorem matrixLazyMarkov_defect_norm_sq_le (X : CMatrix d) :
    hsNorm (X - matrixLazyMarkov U X) ^ 2 ≤
      (normalizedTrace (star X * (X - matrixLazyMarkov U X))).re := by
  let : CompleteSpace (FiniteMatrixHilbert d) := FiniteDimensional.complete ℂ (FiniteMatrixHilbert d)
  have he := lazyHilbertAverage_defect_norm_sq_le
    (fun j => matrixConjugationHilbertEquiv (U j)) (finiteMatrixHilbertEquiv d X)
  simpa only [← matrixLazyMarkov_hilbert, ← map_sub, finiteMatrixHilbert_inner, finiteMatrixHilbert_norm] using he

theorem matrixLazyMarkov_trace_positive (X : CMatrix d) :
    0 ≤ normalizedTrace (star (matrixLazyMarkov U X) * X) := by
  have hp := (ContinuousLinearMap.nonneg_iff_isPositive.mp
    (lazyHilbertAverage_nonneg (fun j => matrixConjugationHilbertEquiv (U j)))).inner_nonneg_left
      (finiteMatrixHilbertEquiv d X)
  simpa only [← matrixLazyMarkov_hilbert, finiteMatrixHilbert_inner] using hp

theorem matrixLazyMarkov_trace_defect_positive (X : CMatrix d) :
    0 ≤ normalizedTrace (star (X - matrixLazyMarkov U X) * X) := by
  have hp := (ContinuousLinearMap.le_def.mp
    (lazyHilbertAverage_le_one (fun j => matrixConjugationHilbertEquiv (U j)))).inner_nonneg_left
      (finiteMatrixHilbertEquiv d X)
  simpa only [sub_apply, one_apply_eq_self, ← matrixLazyMarkov_hilbert, ← map_sub, finiteMatrixHilbert_inner] using hp

theorem matrixLazyMarkov_fixed_iff (X : CMatrix d) :
    matrixLazyMarkov U X = X ↔ ∀ j, Commute (U j).val X := by
  rw [← (finiteMatrixHilbertEquiv d).injective.eq_iff, matrixLazyMarkov_hilbert,
    lazyHilbertAverage_fixed_iff]
  apply forall_congr'
  intro j
  rw [matrixConjugationHilbertEquiv_apply, matrixConjugationHilbert_embedding,
    (finiteMatrixHilbertEquiv d).injective.eq_iff]
  exact (commute_unitary_iff_star_right_conjugate (U j).prop).symm

@[simp] theorem matrixLazyMarkov_one : matrixLazyMarkov U 1 = 1 :=
  (matrixLazyMarkov_fixed_iff U 1).mpr (fun j => Commute.one_right (U j).val)

@[simp] theorem matrixLazyMarkov_trace (X : CMatrix d) :
    normalizedTrace (matrixLazyMarkov U X) = normalizedTrace X := by
  have hp := matrixLazyMarkov_pairing U 1 X
  simpa only [matrixLazyMarkov_one, star_one, one_mul] using hp.symm

end ThomGame.Analysis
