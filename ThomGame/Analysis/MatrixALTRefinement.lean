module

public import ThomGame.Analysis.MatrixScalarGapPartition
public import ThomGame.Analysis.MatrixALTPrunedDecomposition

/-!
# Refinement of the actual ALT decomposition

The bad block is replaced by its spectral rank-one pieces. Every
nonzero block now has the requested scalar gap. The unitary tuple
and its perturbation bound remain exactly the constructed ones.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d h : Nat}

structure MatrixALTDecomposition (U : Fin h → UnitaryMatrix d) (κ η : ℝ) where
  T : Fin (h + h) → UnitaryMatrix d
  partition : MatrixScalarGapPartition T (κ ^ 2 / 2 ^ 28)
  length_le : partition.n ≤ 9 * d
  perturbation : (∑ j, hsNorm ((T j).val - (Fin.append U U j).val) ^ 2) ≤
    (h : ℝ) * altPrunedEditBound κ η

theorem exists_matrixALT_refinement [NeZero d] (U : Fin h → UnitaryMatrix d) {κ η : ℝ}
    (dec : MatrixALTPrunedDecomposition U κ η) : Nonempty (MatrixALTDecomposition U κ η) := by
  obtain ⟨Q, hQ⟩ := exists_matrixScalarGapPartition_refinement dec.T (κ ^ 2 / 2 ^ 28) dec.E
    dec.projection dec.orthogonal dec.sum_one dec.reducing dec.bad_identity dec.scalar_gap
  refine ⟨{
    T := dec.T, partition := Q, length_le := ?_, perturbation := dec.perturbation }⟩
  rw [hQ]
  have hn := dec.length_le
  omega

end ThomGame.Analysis
