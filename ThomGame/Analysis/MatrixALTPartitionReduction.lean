module

public import ThomGame.Analysis.MatrixOrthogonalProjectionEnergy
public import ThomGame.Analysis.MatrixPartitionUnitaryReduction
public import ThomGame.Analysis.MatrixALTOrthogonalSelection

/-!
# Actual reducing unitaries for the corrected ALT partition

The complement of the initial supports is included in the partition.
Reduction on every block preserves the quadratic error in eta.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d h : Nat} [NeZero h]

omit [NeZero h] in
theorem MatrixALTOrthogonalSelection.completed_partition_energy (U : Fin h → UnitaryMatrix d)
    {κ α η : ℝ} {R : CMatrix d} (sel : MatrixALTOrthogonalSelection U κ α η R) :
    (∑ i, matrixCoordinateEnergy U
      (matrixProjectionCompletion (fun j => (sel.V j)ᴴ * sel.V j) i)) ≤ 9472 * η ^ 2 := by
  have he := matrixCoordinateEnergy_orthogonal_completion_le U (fun j => (sel.V j)ᴴ * sel.V j)
    sel.initial_projection sel.initial_orthogonal
  linarith only [he, sel.initial_energy]

theorem MatrixALTOrthogonalSelection.exists_reducing_tuple (U : Fin h → UnitaryMatrix d)
    {κ α η : ℝ} {R : CMatrix d} (sel : MatrixALTOrthogonalSelection U κ α η R) :
    ∃ W : Fin h → UnitaryMatrix d,
      (∀ i j, Commute (matrixProjectionCompletion (fun k => (sel.V k)ᴴ * sel.V k) i) (W j).val) ∧
      (∑ j, hsNorm ((W j).val - (U j).val) ^ 2) ≤ 37888 * (h : ℝ) * η ^ 2 := by
  let E := fun j => (sel.V j)ᴴ * sel.V j
  obtain ⟨W, hred, hdist⟩ := exists_matrixPartition_reducing_tuple (matrixProjectionCompletion E)
    (matrixProjectionCompletion_isStarProjection E sel.initial_projection sel.initial_orthogonal)
    (matrixProjectionCompletion_orthogonal E sel.initial_projection sel.initial_orthogonal)
    (matrixProjectionCompletion_sum E) U
  refine ⟨W, hred, ?_⟩
  rw [hdist]
  have he := mul_le_mul_of_nonneg_left (sel.completed_partition_energy U)
    (show (0 : ℝ) ≤ 4 * h by positivity)
  convert he using 1
  ring

end ThomGame.Analysis
