module

public import ThomGame.Analysis.MatrixProjectionDeletionEnergy
public import ThomGame.Analysis.MatrixProjectionCompletion

/-!
# Energy adds inside orthogonal reducing blocks

Commutators of subprojections in distinct reducing blocks are
orthogonal. Hence the complementary bad block has energy equal to
the sum of the retained-block energies.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d h : Nat} {μ : Type*} [Fintype μ]

omit [Fintype μ] in
theorem matrixProjection_reducing_commutator_left {P e A : CMatrix d}
    (hP : IsStarProjection P) (he : IsStarProjection e) (hle : e ≤ P) (hred : Commute P A) :
    P * (A * e - e * A) = A * e - e * A := by
  have hPe := (he.le_iff_mul_eq_right hP).mp hle
  rw [Matrix.mul_sub, ← Matrix.mul_assoc P A, hred.eq,
    Matrix.mul_assoc A P, hPe, ← Matrix.mul_assoc P e, hPe]

theorem matrixCoordinateEnergy_reducing_sum (U : Fin h → UnitaryMatrix d) (P e : μ → CMatrix d)
    (hP : ∀ i, IsStarProjection (P i)) (he : ∀ i, IsStarProjection (e i))
    (hle : ∀ i, e i ≤ P i) (horth : Pairwise (fun i j => P i * P j = 0))
    (hred : ∀ i j, Commute (P i) (U j).val) :
    matrixCoordinateEnergy U (∑ i, e i) = ∑ i, matrixCoordinateEnergy U (e i) := by
  have hj (j : Fin h) : hsNorm ((U j).val * (∑ i, e i) - (∑ i, e i) * (U j).val) ^ 2 =
      ∑ i, hsNorm ((U j).val * e i - e i * (U j).val) ^ 2 := by
    rw [Matrix.mul_sum, Matrix.sum_mul, ← Finset.sum_sub_distrib]
    have hh := rectHSNorm_orthogonal_sum_sq d (fun i => (U j).val * e i - e i * (U j).val) (by
      intro i k hik
      have hi := matrixProjection_reducing_commutator_left (hP i) (he i) (hle i) (hred i j)
      have hi' : ((U j).val * e i - e i * (U j).val)ᴴ * P i =
          ((U j).val * e i - e i * (U j).val)ᴴ := by
        simpa only [Matrix.conjTranspose_mul, (hP i).isSelfAdjoint.isHermitian.eq] using
          congrArg Matrix.conjTranspose hi
      exact matrixCorner_cross_mul hi'
        (matrixProjection_reducing_commutator_left (hP k) (he k) (hle k) (hred k j)) (horth hik))
    simpa only [rectHSNorm_eq_hsNorm] using hh
  simp only [matrixCoordinateEnergy, hj, ← Finset.mul_sum]
  rw [Finset.sum_comm]

theorem matrixCoordinateEnergy_reducing_complement (U : Fin h → UnitaryMatrix d) (P e : μ → CMatrix d)
    (hP : ∀ i, IsStarProjection (P i)) (he : ∀ i, IsStarProjection (e i))
    (hle : ∀ i, e i ≤ P i) (horth : Pairwise (fun i j => P i * P j = 0))
    (hred : ∀ i j, Commute (P i) (U j).val) :
    matrixCoordinateEnergy U (1 - ∑ i, e i) = ∑ i, matrixCoordinateEnergy U (e i) := by
  rw [matrixCoordinateEnergy_reducing_sub U (fun j => Commute.one_left (U j).val)]
  exact matrixCoordinateEnergy_reducing_sum U P e hP he hle horth hred

theorem matrixCoordinateEnergy_reducing_completion (U : Fin h → UnitaryMatrix d) (P e : μ → CMatrix d)
    (hP : ∀ i, IsStarProjection (P i)) (he : ∀ i, IsStarProjection (e i))
    (hle : ∀ i, e i ≤ P i) (horth : Pairwise (fun i j => P i * P j = 0))
    (hred : ∀ i j, Commute (P i) (U j).val) :
    (∑ i, matrixCoordinateEnergy U (matrixProjectionCompletion e i)) =
      2 * ∑ i, matrixCoordinateEnergy U (e i) := by
  rw [Fintype.sum_option]
  simp only [matrixProjectionCompletion_none, matrixProjectionCompletion_some]
  rw [matrixCoordinateEnergy_reducing_complement U P e hP he hle horth hred]
  ring

end ThomGame.Analysis
