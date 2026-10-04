module

public import ThomGame.Analysis.MatrixScalarGapPartition

/-!
# Omitting zero blocks and reindexing a scalar-gap partition

The nonzero blocks are enumerated by an actual equivalence with Fin.
The unitary tuple, the matrices, and the scalar gap are preserved.
The number of remaining blocks is bounded by the ambient dimension.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d h : Nat}

theorem MatrixScalarGapPartition.length_le_of_nonzero (U : Fin h → UnitaryMatrix d) {c : ℝ}
    (Q : MatrixScalarGapPartition U c) (hne : ∀ i, Q.E i ≠ 0) : Q.n ≤ d := by
  have hr := matrixProjection_sum_rank Q.E Q.projection Q.orthogonal
  rw [Q.sum_one, Matrix.rank_one, Fintype.card_fin] at hr
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Nat.succ_le_of_lt (matrixProjection_rank_pos (Q.projection i) (hne i)))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at he
  omega

theorem MatrixScalarGapPartition.exists_nonzero (U : Fin h → UnitaryMatrix d) {c : ℝ}
    (P : MatrixScalarGapPartition U c) :
    ∃ Q : MatrixScalarGapPartition U c, (∀ i, Q.E i ≠ 0) ∧ Q.n ≤ d ∧
      (∀ i, ∃ j, Q.E i = P.E j) := by
  classical
  let α := {i : Fin P.n // P.E i ≠ 0}
  let e : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  let E : Fin (Fintype.card α) → CMatrix d := fun i => P.E (e i).val
  have hE i : IsStarProjection (E i) := P.projection _
  have hne i : E i ≠ 0 := (e i).property
  have horth : Pairwise (fun i j => E i * E j = 0) := by
    intro i j hij
    apply P.orthogonal
    intro he
    exact hij (e.injective (Subtype.ext he))
  have hsum : ∑ i, E i = 1 := by
    have hzero : (∑ i : {i : Fin P.n // ¬P.E i ≠ 0}, P.E i.val) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact not_ne_iff.mp i.property
    have hs := Fintype.sum_subtype_add_sum_subtype (fun i => P.E i ≠ 0) P.E
    rw [hzero, add_zero, P.sum_one] at hs
    change (∑ i, (fun j : α => P.E j.val) (e i)) = 1
    exact (e.sum_comp (fun j : α => P.E j.val)).trans hs
  let Q : MatrixScalarGapPartition U c := {
    n := Fintype.card α, E := E, projection := hE, orthogonal := horth, sum_one := hsum,
    reducing := fun i => P.reducing (e i).val, scalar_gap := fun i => P.scalar_gap (e i).val }
  exact ⟨Q, hne, Q.length_le_of_nonzero U hne, fun i => ⟨(e i).val, rfl⟩⟩

end ThomGame.Analysis
