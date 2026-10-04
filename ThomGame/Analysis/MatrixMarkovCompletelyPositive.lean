module

public import ThomGame.Analysis.MatrixMarkovPowers
public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-!
# Complete positivity of the actual Markov powers

Positivity is proved at every matrix amplification, using the actual
unitary conjugation automorphisms and the nonnegative Markov weights.
The resulting maps use mathlib's standard completely positive map type.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder CStarAlgebra

variable {d h : Nat}

theorem cstarMatrix_sum_apply {ι m n A : Type*} [AddCommMonoid A] (s : Finset ι)
    (F : ι → CStarMatrix m n A) (i : m) (j : n) :
    (∑ a ∈ s, F a) i j = ∑ a ∈ s, F a i j :=
  map_sum ({ toFun := fun M => M i j, map_zero' := rfl, map_add' := fun _ _ => rfl } :
    CStarMatrix m n A →+ A) F s

theorem matrixUnitaryConjugation_amplification_nonneg (U : UnitaryMatrix d) (k : Nat)
    (M : CStarMatrix (Fin k) (Fin k) (CMatrix d)) (hM : 0 ≤ M) :
    0 ≤ M.map (matrixUnitaryConjugation U) := by
  exact CompletelyPositiveMapClass.map_cstarMatrix_nonneg'
    (Unitary.conjStarAlgAut ℂ (CMatrix d) U) k M hM

theorem matrixLazyMarkov_amplification (U : Fin h → UnitaryMatrix d) (k : Nat)
    (M : CStarMatrix (Fin k) (Fin k) (CMatrix d)) :
    M.map (matrixLazyMarkov U) = ((1 / 2 : ℝ) : ℂ) • M + (lazyMarkovWeight h : ℂ) •
      ∑ j, (M.map (matrixUnitaryConjugation (U j)) + M.map (matrixUnitaryConjugation (U j)⁻¹)) := by
  apply CStarMatrix.ext
  intro i j
  simp only [CStarMatrix.map_apply, matrixLazyMarkov_apply, CStarMatrix.add_apply,
    CStarMatrix.smul_apply, cstarMatrix_sum_apply]

theorem matrixLazyMarkov_amplification_nonneg (U : Fin h → UnitaryMatrix d) (k : Nat)
    (M : CStarMatrix (Fin k) (Fin k) (CMatrix d)) (hM : 0 ≤ M) :
    0 ≤ M.map (matrixLazyMarkov U) := by
  rw [matrixLazyMarkov_amplification]
  apply add_nonneg
  · exact smul_nonneg (by exact_mod_cast (show (0 : ℝ) ≤ 1 / 2 by norm_num)) hM
  · apply smul_nonneg
    · exact_mod_cast lazyMarkovWeight_nonneg h
    · apply Finset.sum_nonneg
      intro j _
      exact add_nonneg (matrixUnitaryConjugation_amplification_nonneg (U j) k M hM)
        (matrixUnitaryConjugation_amplification_nonneg (U j)⁻¹ k M hM)

noncomputable def matrixLazyMarkovCP (U : Fin h → UnitaryMatrix d) : CMatrix d →CP CMatrix d where
  toLinearMap := matrixLazyMarkov U
  map_cstarMatrix_nonneg' := matrixLazyMarkov_amplification_nonneg U

@[simp] theorem matrixLazyMarkovCP_toLinearMap (U : Fin h → UnitaryMatrix d) :
    (matrixLazyMarkovCP U).toLinearMap = matrixLazyMarkov U := rfl

theorem matrixLazyMarkov_pow_amplification_nonneg (U : Fin h → UnitaryMatrix d) (n k : Nat)
    (M : CStarMatrix (Fin k) (Fin k) (CMatrix d)) (hM : 0 ≤ M) :
    0 ≤ M.map (matrixLazyMarkov U ^ n) := by
  induction n with
  | zero => exact hM
  | succ n ih =>
      have he : M.map (matrixLazyMarkov U ^ (n + 1)) =
          (M.map (matrixLazyMarkov U ^ n)).map (matrixLazyMarkov U) := by
        ext i j
        simp only [CStarMatrix.map_apply, pow_succ', Module.End.mul_apply]
      rw [he]
      exact matrixLazyMarkov_amplification_nonneg U k _ ih

noncomputable def matrixMarkovPowerCP (U : Fin h → UnitaryMatrix d) (n : Nat) :
    CMatrix d →CP CMatrix d where
  toLinearMap := matrixLazyMarkov U ^ n
  map_cstarMatrix_nonneg' := matrixLazyMarkov_pow_amplification_nonneg U n

@[simp] theorem matrixMarkovPowerCP_toLinearMap (U : Fin h → UnitaryMatrix d) (n : Nat) :
    (matrixMarkovPowerCP U n).toLinearMap = matrixLazyMarkov U ^ n := rfl

end ThomGame.Analysis
