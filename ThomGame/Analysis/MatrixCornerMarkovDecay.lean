module

public import ThomGame.Analysis.MatrixCornerTraceZero
public import ThomGame.Analysis.MatrixScalarDiagonalExpectation

/-!
# Sharp geometric scalar approximation on every ALT corner

The corner spectral gap controls the actual Markov powers with constant
one. The input and output use the original ambient normalized HS norm.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {d h : Nat}

noncomputable def matrixCornerCenter (P X : CMatrix d) : CMatrix d :=
  X - (normalizedTrace X / normalizedTrace P) • P

theorem matrixCornerCenter_support {P : CMatrix d} (hP : IsStarProjection P)
    (X : CMatrix d) (hleft : P * X = X) (hright : X * P = X) :
    P * matrixCornerCenter P X = matrixCornerCenter P X ∧
      matrixCornerCenter P X * P = matrixCornerCenter P X := by
  constructor <;> simp only [matrixCornerCenter, mul_sub, sub_mul, mul_smul_comm,
    smul_mul_assoc, hleft, hright, hP.isIdempotentElem.eq]

variable [NeZero d]

theorem matrixCornerCenter_trace {P : CMatrix d} (hP : IsStarProjection P) (hne : P ≠ 0)
    (X : CMatrix d) : normalizedTrace (matrixCornerCenter P X) = 0 := by
  rw [matrixCornerCenter, normalizedTrace_sub, normalizedTrace_smul,
    div_mul_cancel₀ _ (normalizedTrace_projection_ne_zero hP hne), sub_self]

theorem matrixTraceProjection_defect_hsNorm_le (S : StarSubalgebra ℂ (CMatrix d)) (X : CMatrix d) :
    hsNorm (X - matrixTraceProjection S X) ≤ hsNorm X := by
  rw [← finiteMatrixHilbert_norm, ← finiteMatrixHilbert_norm, map_sub, matrixTraceProjection_embedding,
    ← Submodule.starProjection_orthogonal_val]
  exact Submodule.norm_starProjection_apply_le _ _

theorem MatrixScalarGapPartition.cornerCenter_hsNorm_le {U : Fin h → UnitaryMatrix d} {c : ℝ}
    (Q : MatrixScalarGapPartition U c) (i : Fin Q.n) (X : CMatrix d) (hleft : Q.E i * X = X) :
    hsNorm (matrixCornerCenter (Q.E i) X) ≤ hsNorm X := by
  have he : matrixCornerCenter (Q.E i) X = X - matrixTraceProjection (matrixPartitionScalarAlgebra Q.E) X := by
    rw [← matrixPartitionScalarExpectation_eq_traceProjection Q.E Q.projection Q.orthogonal Q.sum_one,
      matrixPartitionScalarExpectation_corner Q.E Q.orthogonal i X hleft]
    rfl
  rw [he]
  exact matrixTraceProjection_defect_hsNorm_le _ X

variable [NeZero h]

theorem matrixLazyMarkov_pow_reducing_projection (U : Fin h → UnitaryMatrix d) (P : CMatrix d)
    (hred : ∀ j, Commute P (U j).val) (n : Nat) : (matrixLazyMarkov U ^ n) P = P := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      exact (matrixLazyMarkov_fixed_iff U P).mpr (fun j => (hred j).symm)

theorem matrixLazyMarkov_pow_center (U : Fin h → UnitaryMatrix d) (P : CMatrix d)
    (hred : ∀ j, Commute P (U j).val) (n : Nat) (X : CMatrix d) :
    (matrixLazyMarkov U ^ n) (matrixCornerCenter P X) =
      (matrixLazyMarkov U ^ n) X - (normalizedTrace X / normalizedTrace P) • P := by
  rw [matrixCornerCenter, map_sub, map_smul, matrixLazyMarkov_pow_reducing_projection U P hred]

theorem MatrixScalarGapPartition.corner_markov_pow_scalar_le {U : Fin h → UnitaryMatrix d} {c : ℝ}
    (Q : MatrixScalarGapPartition U c) (hc : c ≤ 1) (i : Fin Q.n) (hi : Q.E i ≠ 0)
    (n : Nat) (X : CMatrix d) (hleft : Q.E i * X = X) (hright : X * Q.E i = X) :
    hsNorm ((matrixLazyMarkov U ^ n) X - (normalizedTrace X / normalizedTrace (Q.E i)) • Q.E i) ≤
      (1 - c) ^ n * hsNorm X := by
  have hs := matrixCornerCenter_support (Q.projection i) X hleft hright
  have ht := matrixCornerCenter_trace (Q.projection i) hi X
  have hg : ∀ Y : CMatrix d, Q.E i * Y = Y → Y * Q.E i = Y → normalizedTrace Y = 0 →
      c * hsNorm Y ^ 2 ≤ matrixCoordinateEnergy U Y := by
    intro Y hl hr htr
    simpa only [htr, zero_div, zero_smul, sub_zero] using Q.scalar_gap i hi Y hl hr
  have he := matrixLazyMarkov_traceZero_corner_pow_le U (Q.E i) (Q.reducing i) c hc hg
    n (matrixCornerCenter (Q.E i) X) hs.1 hs.2 ht
  rw [matrixLazyMarkov_pow_center U (Q.E i) (Q.reducing i)] at he
  exact he.trans (mul_le_mul_of_nonneg_left (Q.cornerCenter_hsNorm_le i X hleft)
    (pow_nonneg (sub_nonneg.mpr hc) n))

end ThomGame.Analysis
