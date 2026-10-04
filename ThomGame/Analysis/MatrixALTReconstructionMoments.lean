module

public import ThomGame.Analysis.MatrixBimoduleRectangles
public import ThomGame.Analysis.MatrixScalarMixingError
public import ThomGame.Analysis.MatrixUCPRectangularMoments

/-!
# Normalized rectangular eigenvectors with the actual ALT moment bounds

Every nonzero rectangular eigenvector is explicitly rescaled to the
larger corner rank. The finite maximum defining the actual scalar error
then gives both inequalities (5.4), with no extra moment assumptions.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra

variable {d : Nat} [NeZero d] {μ : Type*} [Fintype μ]

omit [Fintype μ] in
theorem exists_matrixScalarBimodule_rectangular_eigenbasis (F : CMatrix d →CP CMatrix d)
    (hF : F 1 = 1) (htrace : ∀ X, normalizedTrace (F X) = normalizedTrace X)
    (E : μ → CMatrix d)
    (hbimod : ∀ A X B, A ∈ matrixPartitionScalarAlgebra E → B ∈ matrixPartitionScalarAlgebra E →
      F (A * X * B) = A * F X * B)
    (hpair : ∀ X Y, normalizedTrace (star (F X) * Y) = normalizedTrace (star X * F Y))
    (i j : μ) :
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℂ (matrixRectangleHilbert (E i) (E j)))) ℂ
        (matrixRectangleHilbert (E i) (E j)),
      ∃ eig : Fin (Module.finrank ℂ (matrixRectangleHilbert (E i) (E j))) → ℝ,
        ∀ k, |eig k| ≤ 1 ∧
          F ((finiteMatrixHilbertEquiv d).symm (b k).val) =
            (eig k : ℂ) • (finiteMatrixHilbertEquiv d).symm (b k).val := by
  have hinv := matrixBimodule_rectangle_invariant (matrixPartitionScalarAlgebra E) F.toLinearMap hbimod
    (E i) (E j) (matrixPartitionScalarAlgebra_projection_mem E i) (matrixPartitionScalarAlgebra_projection_mem E j)
  exact exists_matrixRectangle_orthonormal_eigenbasis F hF htrace (E i) (E j) hinv hpair

theorem exists_matrixUCP_rectangular_ALT_5_4 (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (E : μ → CMatrix d) (hE : ∀ i, IsStarProjection (E i)) (hne : ∀ i, E i ≠ 0)
    (i j : μ) (X : CMatrix d) (hX : X ≠ 0) (hleft : E i * X = X) (hright : X * E j = X)
    (lam : ℝ) (heigen : F X = (lam : ℂ) • X) :
    ∃ Y : CMatrix d, Y ≠ 0 ∧ E i * Y = Y ∧ Y * E j = Y ∧
      hsNorm Y ^ 2 = ((max (E i).rank (E j).rank : Nat) : ℝ) / d ∧
      F Y = (lam : ℂ) • Y ∧
      (lam ^ 2 - matrixScalarMixingError E F.toLinearMap) * (Matrix.trace ((star Y * Y) ^ 2)).re ≤
        ((max (E i).rank (E j).rank : Nat) : ℝ) ∧
      lam ^ 2 - matrixScalarMixingError E F.toLinearMap ≤
        ((min (E i).rank (E j).rank : Nat) : ℝ) / ((max (E i).rank (E j).rank : Nat) : ℝ) := by
  let M : ℝ := ((max (E i).rank (E j).rank : Nat) : ℝ) / d
  have hM : 0 < M := div_pos (Nat.cast_pos.mpr
    ((matrixProjection_rank_pos (hE i) (hne i)).trans_le (le_max_left _ _)))
      (Nat.cast_pos.mpr (NeZero.pos d))
  obtain ⟨Y, hY, hl, hr, hm, he⟩ :=
    exists_matrixRectangle_rescaled_eigenvector F.toLinearMap (E i) (E j) X hX hleft hright lam M hM heigen
  have hcorner (k : μ) (Z : CMatrix d) (hzl : E k * Z = Z) (hzr : Z * E k = Z) :
      hsNorm (F Z - (normalizedTrace Z / normalizedTrace (E k)) • E k) ≤
        matrixScalarMixingError E F.toLinearMap * hsNorm Z :=
    matrixScalarMixingError_hsNorm_le E F.toLinearMap k Z hzl hzr
  have hb := matrixUCP_rectangular_ALT_5_4 F hF (E i) (E j) (hE i) (hE j) (hne i) (hne j)
    lam (matrixScalarMixingError E F.toLinearMap) (hcorner i) (hcorner j) Y hY hl hr hm he
  exact ⟨Y, hY, hl, hr, hm, he, hb.1, hb.2⟩

end ThomGame.Analysis
