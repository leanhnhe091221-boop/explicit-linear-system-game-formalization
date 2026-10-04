module

public import ThomGame.Analysis.MatrixStarBlockScalars
public import ThomGame.Analysis.MatrixStarBlockTracePairing

/-!
# Actual coordinates of central block scalars
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} (A : StarSubalgebra ℂ (CMatrix d)) (P : MatrixSubalgebraStarBlocks A)

noncomputable def matrixStarBlockScalarElement (c : Fin P.count → ℝ) : A :=
  ⟨matrixStarBlockScalar A P c, matrixStarBlockScalar_mem A P c⟩

theorem matrixStarBlockScalarElement_equiv (c : Fin P.count → ℝ) (i : Fin P.count) :
    P.equiv (matrixStarBlockScalarElement A P c) i = (c i : ℂ) • (1 : CMatrix (P.size i)) := by
  classical
  have he : matrixStarBlockScalarElement A P c =
      ∑ j, (c j : ℂ) • matrixAlgebraicBlockSupport A P.toAlgebraic j := by
    apply Subtype.ext
    change matrixStarBlockScalar A P c =
      A.subtype (∑ j, (c j : ℂ) • matrixAlgebraicBlockSupport A P.toAlgebraic j)
    simp only [matrixStarBlockScalar, matrixPartitionScalarSum, map_sum, map_smul]
    rfl
  have hs (j : Fin P.count) :
      P.equiv (matrixAlgebraicBlockSupport A P.toAlgebraic j) i = if j = i then 1 else 0 :=
    matrixAlgebraicBlockSupport_equiv A P.toAlgebraic j i
  rw [he]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    hs, smul_ite, smul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem matrixStarBlockSupport_diagonal_sum (i : Fin P.count) :
    matrixStarBlockSupport A P i = ∑ a, A.subtype (matrixStarBlockUnit A P i a a) := by
  change A.subtype (matrixAlgebraicBlockSupport A P.toAlgebraic i) = _
  rw [← matrixAlgebraicBlockUnit_diagonal_sum A P.toAlgebraic i, map_sum]

theorem matrixStarBlockScalar_const (c : ℝ) :
    matrixStarBlockScalar A P (fun _ => c) = (c : ℂ) • (1 : CMatrix d) := by
  simp only [matrixStarBlockScalar, matrixPartitionScalarSum, ← Finset.smul_sum,
    matrixStarBlockSupport_sum]

theorem matrixStarBlockScalar_sub (c b : Fin P.count → ℝ) :
    matrixStarBlockScalar A P c - matrixStarBlockScalar A P b =
      matrixStarBlockScalar A P (c - b) := by
  simp only [matrixStarBlockScalar, matrixPartitionScalarSum, Pi.sub_apply,
    Complex.ofReal_sub, sub_smul, Finset.sum_sub_distrib]

theorem matrixStarBlockScalar_mono {c b : Fin P.count → ℝ} (hcb : ∀ i, c i ≤ b i) :
    matrixStarBlockScalar A P c ≤ matrixStarBlockScalar A P b := by
  apply sub_nonneg.mp
  rw [matrixStarBlockScalar_sub]
  exact matrixStarBlockScalar_nonneg A P _ (fun i => sub_nonneg.mpr (hcb i))

theorem matrixStarBlockScalar_posDef {c : Fin P.count → ℝ} (hc : ∀ i, 0 < c i) :
    (matrixStarBlockScalar A P c).PosDef :=
  (Matrix.nonneg_iff_posSemidef.mp (matrixStarBlockScalar_nonneg A P c (fun i => (hc i).le))).posDef_iff_isUnit.mpr
    (matrixStarBlockScalar_isUnit A P c (fun i => ne_of_gt (hc i)))

end ThomGame.Analysis
