module

public import ThomGame.Analysis.FiniteNoDriftRootWords
public import ThomGame.Analysis.FiniteIsometryAverage
public import ThomGame.Analysis.MatrixLazyMarkov

/-! The canonical finite root tuple has exactly the three-root lazy normalization. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open scoped BigOperators

variable {d r : ℕ} [NeZero d]

def finiteNoDriftCyclicAverage (f : Compressor.Generator → UnitaryMatrix d)
    (σ : Fin r → Compressor.Coeff) (c : Fin 3) :
    FiniteMatrixHilbert d →L[ℂ] FiniteMatrixHilbert d :=
  finiteIsometrySymmetricAverage (fun α : Fin r → ZMod 5 =>
    matrixConjugationHilbertEquiv (Word.eval f (finiteNoDriftRootWord σ c α)))

theorem finiteNoDrift_root_lazy_normalization (f : Compressor.Generator → UnitaryMatrix d)
    (σ : Fin r → Compressor.Coeff) (X : CMatrix d) :
    finiteMatrixHilbertEquiv d (X - matrixLazyMarkov (finiteNoDriftRootTuple f σ) X) =
      (1 / 6 : ℂ) • ∑ c : Fin 3, (finiteMatrixHilbertEquiv d X -
        finiteNoDriftCyclicAverage f σ c (finiteMatrixHilbertEquiv d X)) := by
  classical
  let x := finiteMatrixHilbertEquiv d X
  let U := fun p : FiniteNoDriftRootIndex r =>
    matrixConjugationHilbertEquiv (Word.eval f (finiteNoDriftRootWord σ p.1 p.2))
  let Y := fun c : Fin 3 => ∑ α : Fin r → ZMod 5, (U (c, α) x + (U (c, α)).symm x)
  have havg (c : Fin 3) : finiteNoDriftCyclicAverage f σ c x =
      ((1 / 2 : ℂ) * ((5 : ℂ) ^ r)⁻¹) • Y c := by
    simp only [finiteNoDriftCyclicAverage, finiteIsometrySymmetricAverage_apply,
      finiteIsometryAverage_apply, Fintype.card_fun, ZMod.card, Fintype.card_fin,
      Nat.cast_pow, Nat.cast_ofNat]
    rw [← smul_add, smul_smul, ← Finset.sum_add_distrib]
  have hsum : (∑ j : Fin (3 * 5 ^ r),
      (matrixConjugationHilbertEquiv (finiteNoDriftRootTuple f σ j) x +
        (matrixConjugationHilbertEquiv (finiteNoDriftRootTuple f σ j)).symm x)) = ∑ c, Y c := by
    calc
      _ = ∑ p : FiniteNoDriftRootIndex r, (U p x + (U p).symm x) :=
        Equiv.sum_comp (Fintype.equivFinOfCardEq (finiteNoDriftRootIndex_card r)).symm
          (fun p : FiniteNoDriftRootIndex r => U p x + (U p).symm x)
      _ = ∑ c, Y c := Fintype.sum_prod_type (fun p : FiniteNoDriftRootIndex r => U p x + (U p).symm x)
  have hweight : (lazyMarkovWeight (3 * 5 ^ r) : ℂ) =
      (1 / 12 : ℂ) * ((5 : ℂ) ^ r)⁻¹ := by
    simp only [lazyMarkovWeight, Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_ofNat,
      Complex.ofReal_pow, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [mul_inv_rev, mul_inv_rev]
    ring
  rw [map_sub, matrixLazyMarkov_hilbert, lazyHilbertAverage_apply]
  change x - ((↑(1 / 2 : ℝ) : ℂ) • x + (lazyMarkovWeight (3 * 5 ^ r) : ℂ) • _) =
    (1 / 6 : ℂ) • ∑ c : Fin 3, (x - finiteNoDriftCyclicAverage f σ c x)
  rw [hsum, hweight]
  simp only [havg, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  module

theorem finiteNoDrift_root_energy_normalization (f : Compressor.Generator → UnitaryMatrix d)
    (σ : Fin r → Compressor.Coeff) (X : CMatrix d) :
    matrixCoordinateEnergy (finiteNoDriftRootTuple f σ) X =
      (1 / 6 : ℝ) * (inner ℂ (finiteMatrixHilbertEquiv d X)
        (∑ c : Fin 3, (finiteMatrixHilbertEquiv d X -
          finiteNoDriftCyclicAverage f σ c (finiteMatrixHilbertEquiv d X)))).re := by
  have he := matrixLazyMarkov_energy (finiteNoDriftRootTuple f σ) X
  change (normalizedTrace (star X * (X - matrixLazyMarkov (finiteNoDriftRootTuple f σ) X))).re =
    matrixCoordinateEnergy (finiteNoDriftRootTuple f σ) X at he
  rw [← he, ← finiteMatrixHilbert_inner, finiteNoDrift_root_lazy_normalization, inner_smul_right]
  simp only [Complex.mul_re, show (1 / 6 : ℂ).re = (1 / 6 : ℝ) by norm_num,
    show (1 / 6 : ℂ).im = 0 by norm_num, zero_mul, sub_zero]

theorem finiteNoDrift_root_defect_sq_normalization (f : Compressor.Generator → UnitaryMatrix d)
    (σ : Fin r → Compressor.Coeff) (X : CMatrix d) :
    hsNorm (X - matrixLazyMarkov (finiteNoDriftRootTuple f σ) X) ^ 2 =
      (1 / 36 : ℝ) * ‖∑ c : Fin 3, (finiteMatrixHilbertEquiv d X -
        finiteNoDriftCyclicAverage f σ c (finiteMatrixHilbertEquiv d X))‖ ^ 2 := by
  have hn := congrArg norm (finiteNoDrift_root_lazy_normalization f σ X)
  rw [finiteMatrixHilbert_norm, norm_smul] at hn
  rw [show ‖(1 / 6 : ℂ)‖ = (1 / 6 : ℝ) by norm_num] at hn
  rw [hn]
  ring

end ThomGame.Analysis
