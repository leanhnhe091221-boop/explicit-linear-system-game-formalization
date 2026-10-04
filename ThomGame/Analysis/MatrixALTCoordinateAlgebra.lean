module

public import ThomGame.Analysis.MatrixALTUnitOrZeroBound
public import ThomGame.Analysis.MatrixUnitCompletionAlgebra
public import ThomGame.Analysis.MatrixRectangleSpectrum
public import ThomGame.Analysis.MatrixUnitCompletionDiagonal
public import ThomGame.Analysis.MatrixUnitCompletionExpectation

/-!
# Actual pruned coordinate algebras and uniform rectangular approximation

The original small-defect channel produces the same retained blocks,
matrix units, support and completed matrix star subalgebra. All block
operator estimates use these constructed matrix units.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat} [NeZero d]

theorem exists_matrixALT_coordinate_algebra {μ : Type*} [Fintype μ] [DecidableEq μ]
    (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ X, normalizedTrace (F X) = normalizedTrace X)
    (hpair : ∀ X Y, normalizedTrace (star (F X) * Y) = normalizedTrace (star X * F Y))
    (E : μ → CMatrix d) (hE : ∀ i, IsStarProjection (E i)) (hne : ∀ i, E i ≠ 0)
    (horth : Pairwise (fun i j => E i * E j = 0)) (hsum : ∑ i, E i = 1)
    (hbimod : ∀ A X B, A ∈ matrixPartitionScalarAlgebra E → B ∈ matrixPartitionScalarAlgebra E →
      F (A * X * B) = A * F X * B)
    (rho : ℝ) (hrho : 0 < rho) (hsmall : rho ≤ 1 / 1024)
    (hsigma : matrixScalarMixingError E F.toLinearMap ≤ rho ^ 4)
    (hdelta : matrixMixedNorm (F.toLinearMap.comp F.toLinearMap - F.toLinearMap) ≤ rho ^ 4) :
    ∃ S : Finset μ, ∃ (o : S → S) (W : S → S → CMatrix d) (A : StarSubalgebra ℂ (CMatrix d)),
      IsStarProjection (∑ i : S, E i.val) ∧
      (normalizedTrace (1 - ∑ i : S, E i.val)).re ≤ 64 * rho ^ 2 ∧
      IsStarProjection (∑ i, W i i) ∧ (∑ i, W i i) ≤ (∑ i : S, E i.val) ∧
      (normalizedTrace (1 - ∑ i, W i i)).re ≤ 64 * rho ^ 2 + 2 * rho ∧
      (∀ i, IsStarProjection (W i i) ∧ W i i ≤ E i.val ∧
        (1 - 2 * rho) * (normalizedTrace (E i.val)).re ≤ (normalizedTrace (W i i)).re) ∧
      (∀ i j, star (W i j) = W j i) ∧
      (∀ i j, E i.val * W i j = W i j ∧ W i j * E j.val = W i j) ∧
      (∀ i j, W i j ≠ 0 ↔ o i = o j) ∧
      (∀ i j k l, o i = o j → W i j * W k l = if j = k then W i l else 0) ∧
      (∀ i j, W i j ∈ A) ∧
      matrixPartitionScalarAlgebra E ≤ A ∧
      (∀ X, X ∈ A ↔ ∃ Y ∈ matrixUnitSpan W, ∃ Z : CMatrix d,
        ((1 - ∑ i, W i i) * Z = Z ∧ Z * (1 - ∑ i, W i i) = Z) ∧ Y + Z = X) ∧
      (∀ X, matrixTraceProjection A X = matrixSubmoduleTraceProjection (matrixUnitSpan W) X +
        (1 - ∑ i, W i i) * X * (1 - ∑ i, W i i)) ∧
      (∀ i j (hl : E i.val * W i j = W i j) (hr : W i j * E j.val = W i j),
        ‖matrixScalarBimoduleRectangleMap F.toLinearMap E hbimod i.val j.val -
          matrixRectangleLineProjection (E i.val) (E j.val) (W i j) hl hr‖ ≤ 113 * Real.sqrt rho) := by
  obtain ⟨S, o, q, W, hp, hpmass, hbands, hQ, hQp, hQmass, hiff, _, _, _,
    hq, hdiag, hstar, hsupport, hneW, hmul, herr⟩ :=
    exists_matrixALT_pruned_matrix_units F hF htrace hpair E hE hne horth hsum hbimod
      rho hrho hsmall hsigma hdelta
  have hzero i j (hij : o i ≠ o j) : W i j = 0 := by
    by_contra h
    exact hij ((hneW i j).mp h)
  let A := matrixUnitCompletionAlgebra o W hzero hmul hstar
  have hsumq : (∑ i, W i i) = ∑ i, q i := Finset.sum_congr rfl (fun i _ => hdiag i)
  refine ⟨S, o, W, A, hp, hpmass, hsumq.symm ▸ hQ, hsumq.symm ▸ hQp,
    hsumq.symm ▸ hQmass, ?_, hstar, hsupport, hneW, hmul, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hdiag i]
    exact ⟨(hq i).1, (hq i).2.1, (hq i).2.2.2.2⟩
  · exact matrixUnitCompletionAlgebra_unit_mem o W hzero hmul hstar
  · exact matrixPartitionScalarAlgebra_le_unitCompletion E hE horth S o W hzero hmul hstar hsupport
  · exact mem_matrixUnitCompletionAlgebra_iff o W hzero hmul hstar
  · exact matrixUnitCompletionAlgebra_expectation o W hzero hmul hstar
  · intro i j hl hr
    have hfix : hsNorm (F (W i j) - W i j) ^ 2 ≤ 288 * rho * hsNorm (W i j) ^ 2 := by
      by_cases hij : o i = o j
      · rw [(herr i j hij).1]
        exact (herr i j hij).2.2
      · rw [hzero i j hij, map_zero, sub_zero, hsNorm_zero]
        norm_num
    exact matrixUCP_unit_or_zero_projection_bound F hF htrace hpair E hE hne i.val j.val
      (matrixBimodule_rectangle_invariant (matrixPartitionScalarAlgebra E) F.toLinearMap hbimod
        (E i.val) (E j.val) (matrixPartitionScalarAlgebra_projection_mem E i.val)
          (matrixPartitionScalarAlgebra_projection_mem E j.val))
      rho hrho.le hsmall hsigma (hbands i.val i.property j.val j.property)
        (W i j) hl hr ((hneW i j).trans (hiff i j).symm) hfix

end ThomGame.Analysis
