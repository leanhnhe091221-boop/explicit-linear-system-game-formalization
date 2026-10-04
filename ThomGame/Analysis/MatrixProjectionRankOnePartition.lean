module

public import ThomGame.Analysis.MatrixRankOneCorners

/-!
# Actual rank-one refinement of a matrix projection

The spectral eigenvectors define a finite orthogonal family summing
to the projection. Zero eigenvalues contribute zero blocks; every
nonzero piece has rank exactly one.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat}

theorem matrixBasisProjection_empty (U : UnitaryMatrix d) :
    matrixBasisProjection U ∅ = 0 := by
  simp [matrixBasisProjection]

theorem matrixBasisProjection_singleton_orthogonal (U : UnitaryMatrix d) {i j : Fin d} (hij : i ≠ j) :
    matrixBasisProjection U {i} * matrixBasisProjection U {j} = 0 := by
  rw [matrixBasisProjection, matrixBasisProjection, ← map_mul, Matrix.diagonal_mul_diagonal]
  have he : Matrix.diagonal (fun k : Fin d =>
      (if k ∈ ({i} : Finset (Fin d)) then (1 : ℂ) else 0) *
        (if k ∈ ({j} : Finset (Fin d)) then (1 : ℂ) else 0)) = 0 := by
    ext k l
    by_cases hki : k = i
    · subst k
      simp [Matrix.diagonal_apply, hij]
    · simp [Matrix.diagonal_apply, hki]
  rw [he, map_zero]

noncomputable def matrixProjectionRankOnePiece {P : CMatrix d} (hP : IsStarProjection P) (i : Fin d) :
    CMatrix d := Unitary.conjStarAlgAut ℂ (CMatrix d) hP.isSelfAdjoint.isHermitian.eigenvectorUnitary
      (Matrix.diagonal (fun j => if j = i then (hP.isSelfAdjoint.isHermitian.eigenvalues i : ℂ) else 0))

theorem matrixProjectionRankOnePiece_eq {P : CMatrix d} (hP : IsStarProjection P) (i : Fin d) :
    matrixProjectionRankOnePiece hP i =
      if hP.isSelfAdjoint.isHermitian.eigenvalues i = 0 then 0 else
        matrixBasisProjection hP.isSelfAdjoint.isHermitian.eigenvectorUnitary {i} := by
  rcases matrixProjection_eigenvalues_mem hP i with hi | hi
  · simp [matrixProjectionRankOnePiece, hi]
  · simp [matrixProjectionRankOnePiece, matrixBasisProjection, hi]

theorem matrixProjectionRankOnePiece_isStarProjection {P : CMatrix d} (hP : IsStarProjection P) (i : Fin d) :
    IsStarProjection (matrixProjectionRankOnePiece hP i) := by
  rw [matrixProjectionRankOnePiece_eq]
  split_ifs
  · exact IsStarProjection.zero (CMatrix d)
  · exact matrixBasisProjection_isStarProjection _ _

theorem matrixProjectionRankOnePiece_rank_le {P : CMatrix d} (hP : IsStarProjection P) (i : Fin d) :
    (matrixProjectionRankOnePiece hP i).rank ≤ 1 := by
  rw [matrixProjectionRankOnePiece_eq]
  split_ifs
  · simp only [Matrix.rank_zero, Nat.zero_le]
  · simp only [matrixBasisProjection_rank, Finset.card_singleton, le_refl]

theorem matrixProjectionRankOnePiece_rank_eq {P : CMatrix d} (hP : IsStarProjection P) (i : Fin d)
    (hne : matrixProjectionRankOnePiece hP i ≠ 0) : (matrixProjectionRankOnePiece hP i).rank = 1 := by
  have hp := matrixProjection_rank_pos (matrixProjectionRankOnePiece_isStarProjection hP i) hne
  have hl := matrixProjectionRankOnePiece_rank_le hP i
  omega

theorem matrixProjectionRankOnePiece_orthogonal {P : CMatrix d} (hP : IsStarProjection P) :
    Pairwise (fun i j => matrixProjectionRankOnePiece hP i * matrixProjectionRankOnePiece hP j = 0) := by
  intro i j hij
  simp only [matrixProjectionRankOnePiece_eq]
  split_ifs
  · exact Matrix.zero_mul _
  · exact Matrix.zero_mul _
  · exact Matrix.mul_zero _
  · exact matrixBasisProjection_singleton_orthogonal _ hij

theorem matrixProjectionRankOnePiece_sum {P : CMatrix d} (hP : IsStarProjection P) :
    ∑ i, matrixProjectionRankOnePiece hP i = P := by
  classical
  unfold matrixProjectionRankOnePiece
  rw [← map_sum]
  calc
    _ = Unitary.conjStarAlgAut ℂ (CMatrix d) hP.isSelfAdjoint.isHermitian.eigenvectorUnitary
        (Matrix.diagonal (fun i => (hP.isSelfAdjoint.isHermitian.eigenvalues i : ℂ))) := by
      congr 1
      ext i j
      by_cases hij : i = j
      · subst j
        simp [Matrix.sum_apply]
      · simp [Matrix.sum_apply, hij]
    _ = P := hP.isSelfAdjoint.isHermitian.spectral_theorem.symm

theorem matrixProjectionRankOnePiece_le {P : CMatrix d} (hP : IsStarProjection P) (i : Fin d) :
    matrixProjectionRankOnePiece hP i ≤ P := by
  calc
    _ ≤ ∑ j, matrixProjectionRankOnePiece hP j :=
      Finset.single_le_sum (fun j _ => (matrixProjectionRankOnePiece_isStarProjection hP j).nonneg)
        (Finset.mem_univ i)
    _ = P := matrixProjectionRankOnePiece_sum hP

end ThomGame.Analysis
