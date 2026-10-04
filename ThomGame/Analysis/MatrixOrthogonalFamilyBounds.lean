module

public import ThomGame.Analysis.MatrixRandomSignSums
public import ThomGame.Analysis.FiniteRootMeanSquare
public import ThomGame.Analysis.MatrixMarkovDefectBound

/-!
# Uniform defects on orthogonal projection families

The actual signed contraction sums turn a uniform unit-ball defect
into a root-mean-square family bound without a cardinality factor.
The output-energy bound passes to the sum over the family as well.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator

variable {d h : Nat} [NeZero d] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrixOrthogonalFamily_distance_bound (U : Fin h → UnitaryMatrix d)
    (T : CMatrix d →ₗ[ℂ] CMatrix d) (P : ι → CMatrix d)
    (hP : ∀ i, IsStarProjection (P i)) (horth : Pairwise (fun i j => P i * P j = 0))
    (c β : ℝ) (hc : 0 ≤ c) (hβ : 0 ≤ β)
    (hdist : ∀ X, matrixOpNorm X ≤ 1 → hsNorm (X - T X) ≤ c * Real.sqrt (matrixCoordinateEnergy U X) + β) :
    Real.sqrt (∑ i, hsNorm (P i - T (P i)) ^ 2) ≤
      c * Real.sqrt (∑ i, matrixCoordinateEnergy U (P i)) + β := by
  have he := sqrt_expect_sq_le_of_pointwise
    (fun ε : ι → Bool => hsNorm (finiteSignSum P ε - T (finiteSignSum P ε)))
    (fun ε : ι → Bool => Real.sqrt (matrixCoordinateEnergy U (finiteSignSum P ε))) c β
    (fun _ => hsNorm_nonneg _) (fun _ => Real.sqrt_nonneg _) hc hβ
    (fun ε => hdist _ (matrixSignSum_matrixOpNorm_le_one P hP horth ε))
  simpa only [matrixSignSum_expect_defect_sq, Real.sq_sqrt (matrixCoordinateEnergy_nonneg U _),
    matrixSignSum_expect_energy] using he

theorem matrixOrthogonalFamily_energy_bound (U : Fin h → UnitaryMatrix d)
    (T : CMatrix d →ₗ[ℂ] CMatrix d) (P : ι → CMatrix d)
    (hP : ∀ i, IsStarProjection (P i)) (horth : Pairwise (fun i j => P i * P j = 0))
    (β : ℝ) (henergy : ∀ X, matrixOpNorm X ≤ 1 → Real.sqrt (matrixCoordinateEnergy U (T X)) ≤ β) :
    (∑ i, matrixCoordinateEnergy U (T (P i))) ≤ β ^ 2 := by
  rw [← matrixSignSum_expect_map_energy U T P]
  apply Finset.expect_le Finset.univ_nonempty
  intro ε _
  exact (Real.sqrt_le_iff.mp (henergy _ (matrixSignSum_matrixOpNorm_le_one P hP horth ε))).2

theorem matrixMarkovOrthogonalFamily_distance_bound (U : Fin h → UnitaryMatrix d)
    (κ : ℝ) (k : Nat) (P : ι → CMatrix d) (hP : ∀ i, IsStarProjection (P i))
    (horth : Pairwise (fun i j => P i * P j = 0)) :
    Real.sqrt (∑ i, hsNorm (P i - (matrixLazyMarkov U ^ k) (P i)) ^ 2) ≤
      (Real.sqrt κ)⁻¹ * Real.sqrt (∑ i, matrixCoordinateEnergy U (P i)) + matrixMarkovDefectBound U κ k :=
  matrixOrthogonalFamily_distance_bound U (matrixLazyMarkov U ^ k) P hP horth _ _
    (inv_nonneg.mpr (Real.sqrt_nonneg κ)) (matrixMarkovDefectBound_nonneg U κ k)
    (matrixMarkovDefectBound_distance U κ k)

theorem matrixMarkovOrthogonalFamily_energy_bound (U : Fin h → UnitaryMatrix d)
    (κ : ℝ) (k : Nat) (P : ι → CMatrix d) (hP : ∀ i, IsStarProjection (P i))
    (horth : Pairwise (fun i j => P i * P j = 0)) :
    (∑ i, matrixCoordinateEnergy U ((matrixLazyMarkov U ^ k) (P i))) ≤ matrixMarkovDefectBound U κ k ^ 2 :=
  matrixOrthogonalFamily_energy_bound U (matrixLazyMarkov U ^ k) P hP horth _
    (matrixMarkovDefectBound_energy U κ k)

end ThomGame.Analysis
