module

public import ThomGame.Analysis.MatrixPinchingRounding
public import Mathlib.Analysis.CStarAlgebra.Projection

/-!
# Actual subprojections of any smaller rank

A subset of the nonzero eigenvectors of a projection defines an
actual subprojection of the prescribed rank. Real trace formulas
retain an arbitrary original normalization.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrixProjection_eigenvalues_mem {P : Matrix ι ι ℂ} (hP : IsStarProjection P) (i : ι) :
    hP.isSelfAdjoint.isHermitian.eigenvalues i = 0 ∨ hP.isSelfAdjoint.isHermitian.eigenvalues i = 1 := by
  have he := hP.isIdempotentElem.spectrum_subset ℝ
    (hP.isSelfAdjoint.isHermitian.eigenvalues_mem_spectrum_real i)
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using he

theorem matrixTraceReal_projection_rank (r : Nat) {P : Matrix ι ι ℂ} (hP : IsStarProjection P) :
    matrixTraceReal r P = (P.rank : ℝ) / r := by
  classical
  rw [matrixTraceReal, hP.isSelfAdjoint.isHermitian.trace_eq_sum_eigenvalues,
    hP.isSelfAdjoint.isHermitian.rank_eq_card_non_zero_eigs]
  simp only [Complex.re_sum, Fintype.card_subtype, Finset.card_filter,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rcases matrixProjection_eigenvalues_mem hP i with hi | hi <;> simp [hi]

noncomputable def matrixBasisProjection (U : Matrix.unitaryGroup ι ℂ) (S : Finset ι) : Matrix ι ι ℂ :=
  Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U (Matrix.diagonal (fun i => if i ∈ S then 1 else 0))

theorem matrixBasisProjection_isStarProjection (U : Matrix.unitaryGroup ι ℂ) (S : Finset ι) :
    IsStarProjection (matrixBasisProjection U S) := by
  apply IsStarProjection.map _ (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U)
  constructor
  · show Matrix.diagonal (fun i => if i ∈ S then (1 : ℂ) else 0) * _ = _
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    split_ifs <;> simp_all
  · show (Matrix.diagonal (fun i => if i ∈ S then (1 : ℂ) else 0))ᴴ = _
    simp only [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    split_ifs <;> simp_all

theorem matrixBasisProjection_rank (U : Matrix.unitaryGroup ι ℂ) (S : Finset ι) :
    (matrixBasisProjection U S).rank = S.card := by
  classical
  rw [matrixBasisProjection, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star]
  simp [-isUnit_iff_ne_zero, -Unitary.coe_star, Matrix.rank_diagonal,
    Fintype.card_subtype]

theorem exists_matrixSubprojection_rank {P : Matrix ι ι ℂ} (hP : IsStarProjection P)
    (n : Nat) (hn : n ≤ P.rank) :
    ∃ Q : Matrix ι ι ℂ, IsStarProjection Q ∧ Q ≤ P ∧ Q.rank = n := by
  classical
  let H := hP.isSelfAdjoint.isHermitian
  let S : Finset ι := Finset.univ.filter (fun i => H.eigenvalues i ≠ 0)
  have hS : S.card = P.rank := by
    rw [H.rank_eq_card_non_zero_eigs]
    simp [S, Fintype.card_subtype]
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq (hS.symm ▸ hn)
  let Q := matrixBasisProjection H.eigenvectorUnitary T
  have hQ := matrixBasisProjection_isStarProjection H.eigenvectorUnitary T
  refine ⟨Q, hQ, (hQ.le_iff_mul_eq_left hP).mpr ?_, (matrixBasisProjection_rank _ T).trans hT⟩
  change matrixBasisProjection H.eigenvectorUnitary T * P = _
  conv_lhs => rhs; rw [H.spectral_theorem]
  rw [matrixBasisProjection, ← map_mul]
  congr 1
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hi : i ∈ T
  · have hnz : H.eigenvalues i ≠ 0 := (Finset.mem_filter.mp (hTS hi)).2
    have hone : H.eigenvalues i = 1 := (matrixProjection_eigenvalues_mem hP i).resolve_left hnz
    simp [hi, hone]
  · simp [hi]

end ThomGame.Analysis
