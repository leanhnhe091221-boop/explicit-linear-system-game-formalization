module

public import ThomGame.Analysis.MatrixProjectionPieceEnergy

/-!
# The actual orthogonal family and the bounds ALT (3.14)

Starting only from the covering projections and their total trace
and energy bounds, construct all partial isometries in the original
matrix algebra. Their initial projections are orthogonal, their
targets lie below the given projections, and both quantitative bounds
are those of (3.14). The asymptotic parameter choice is a further step.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {μ : Type*} [Fintype μ] [DecidableEq μ] {d h : Nat} [NeZero d] [NeZero h]

theorem exists_matrixOrthogonalFamily_ALT_3_14 {q : μ → CMatrix d}
    (hq : ∀ i, IsStarProjection (q i)) (U : Fin h → UnitaryMatrix d)
    {s a t : ℝ} (htrace : ∑ i, matrixTraceReal d (q i) ≤ 3)
    (henergy : ∑ i, matrixCoordinateEnergy U (q i) ≤ s) (ha : 0 < a) (ht : 1 ≤ t) :
    ∃ V : μ → CMatrix d,
      (∀ i, IsStarProjection ((V i)ᴴ * V i)) ∧
      (∀ i, IsStarProjection (V i * (V i)ᴴ)) ∧
      (∀ i, V i * (V i)ᴴ ≤ q i) ∧
      Pairwise (fun i j => ((V i)ᴴ * V i) * ((V j)ᴴ * V j) = 0) ∧
      (∑ i, matrixCoordinateEnergy U (V i)) ≤
        2 * s + 8 * Real.exp (4 * t) * Real.sqrt s / a + 64 * t ^ (-(1 / 2 : ℝ)) ∧
      (∑ i, matrixCoordinateEnergy U ((V i)ᴴ * V i)) ≤ 4 * ∑ i, matrixCoordinateEnergy U (V i) ∧
      matrixFamilyCoverageDefect (fun i => (V i)ᴴ * V i) - matrixFamilyCoverageDefect q ≤ 4 * a := by
  obtain ⟨Z, hZ, hcomm, hZe, hZcov⟩ := exists_matrixColumn_block_partialIsometry hq U htrace henergy ha ht
  let V := matrixProjectionPiece hq Z
  have hVi (i : μ) : IsStarProjection ((V i)ᴴ * V i) :=
    matrixProjectionPiece_partialIsometry hq hZ hcomm i
  have hVf (i : μ) : IsStarProjection (V i * (V i)ᴴ) := matrixPartialIsometry_final_projection (hVi i)
  have horth : Pairwise (fun i j => ((V i)ᴴ * V i) * ((V j)ᴴ * V j) = 0) :=
    fun _ _ hij => matrixProjectionPiece_orthogonal hq hZ hcomm hij
  refine ⟨V, hVi, hVf, (fun i => matrixProjectionPiece_final_le hq hZ hcomm i), horth, ?_, ?_, ?_⟩
  · calc
      _ ≤ 2 * (∑ i, matrixCoordinateEnergy U (q i)) +
          2 * matrixIntertwiningEnergy d U (fun j => matrixProjectionBlockUnitary d hq (U j)) Z :=
        matrixProjectionPiece_energy_le d hq hZ hcomm U
      _ ≤ 2 * s + 2 * (4 * Real.exp (4 * t) * Real.sqrt s / a + 32 * t ^ (-(1 / 2 : ℝ))) :=
        add_le_add (mul_le_mul_of_nonneg_left henergy (by norm_num))
          (mul_le_mul_of_nonneg_left hZe (by norm_num))
      _ = _ := by ring
  · calc
      _ ≤ ∑ i, 4 * matrixCoordinateEnergy U (V i) :=
        Finset.sum_le_sum fun i _ => matrixCoordinateEnergy_partialIsometry_initial_le U (hVi i)
      _ = _ := by rw [Finset.mul_sum]
  · have he : matrixFamilyCoverageDefect (fun i => (V i)ᴴ * V i) = matrixTraceReal d (1 - Zᴴ * Z) := by
      rw [matrixFamilyCoverageDefect_orthogonal _ hVi horth]
      change (normalizedTrace (1 - ∑ i, (matrixProjectionPiece hq Z i)ᴴ * matrixProjectionPiece hq Z i)).re = _
      rw [matrixProjectionPiece_initial_sum]
      exact normalizedTrace_re _
    rw [he]
    linarith

end ThomGame.Analysis
