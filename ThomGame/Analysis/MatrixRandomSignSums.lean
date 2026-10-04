module

public import ThomGame.Analysis.FiniteRandomSigns
public import ThomGame.Analysis.MatrixMarkovPoincare
public import Mathlib.RingTheory.Idempotents

/-!
# Random signs of orthogonal matrix projections

Every signed sum of orthogonal projections is an actual operator-norm
contraction. Uniform sign averages recover the sum of squared
normalized Hilbert--Schmidt norms and the sum of commutator energies.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {d h : Nat} {ι : Type*} [Fintype ι]

theorem matrixOrthogonalSum_projection (P : ι → CMatrix d) (hP : ∀ i, IsStarProjection (P i))
    (horth : Pairwise (fun i j => P i * P j = 0)) : IsStarProjection (∑ i, P i) := by
  refine ⟨(OrthogonalIdempotents.mk (fun i => (hP i).isIdempotentElem) horth).isIdempotentElem_sum, ?_⟩
  change star (∑ i, P i) = ∑ i, P i
  simp only [star_sum, (hP _).isSelfAdjoint.star_eq]

theorem matrixSignSum_selfAdjoint (P : ι → CMatrix d) (hP : ∀ i, IsStarProjection (P i))
    (ε : ι → Bool) : IsSelfAdjoint (finiteSignSum P ε) := by
  change star (finiteSignSum P ε) = finiteSignSum P ε
  simp only [finiteSignSum, star_sum, star_smul, star_trivial, (hP _).isSelfAdjoint.star_eq]

theorem matrixSignSum_sq (P : ι → CMatrix d) (hP : ∀ i, IsStarProjection (P i))
    (horth : Pairwise (fun i j => P i * P j = 0)) (ε : ι → Bool) :
    finiteSignSum P ε * finiteSignSum P ε = ∑ i, P i := by
  classical
  calc
    _ = ∑ i, ∑ j, (finiteSign (ε i) * finiteSign (ε j)) • (P i * P j) := by
      simp only [finiteSignSum, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
        Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [mul_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · rw [(hP i).isIdempotentElem.eq, ← pow_two, finiteSign_sq, one_smul]
      · intro j _ hji
        rw [horth hji.symm, smul_zero]
      · simp

theorem matrixSignSum_matrixOpNorm_le_one (P : ι → CMatrix d) (hP : ∀ i, IsStarProjection (P i))
    (horth : Pairwise (fun i j => P i * P j = 0)) (ε : ι → Bool) :
    matrixOpNorm (finiteSignSum P ε) ≤ 1 := by
  have hn := IsStarProjection.norm_le _ (matrixOrthogonalSum_projection P hP horth)
  rw [← matrixSignSum_sq P hP horth ε, (matrixSignSum_selfAdjoint P hP ε).norm_mul_self] at hn
  change ‖finiteSignSum P ε‖ ≤ 1
  nlinarith [norm_nonneg (finiteSignSum P ε)]

variable [NeZero d] [DecidableEq ι]

theorem matrixSignSum_expect_hsNorm_sq (X : ι → CMatrix d) :
    (𝔼 ε : ι → Bool, hsNorm (finiteSignSum X ε) ^ 2) = ∑ i, hsNorm (X i) ^ 2 := by
  let : InnerProductSpace ℝ (FiniteMatrixHilbert d) := InnerProductSpace.complexToReal
  have he := finiteSignSum_expect_norm_sq (fun i => finiteMatrixHilbertEquiv d (X i))
  have hmap (ε : ι → Bool) : finiteSignSum (fun i => finiteMatrixHilbertEquiv d (X i)) ε =
      finiteMatrixHilbertEquiv d (finiteSignSum X ε) :=
    (finiteSignSum_map ((finiteMatrixHilbertEquiv d).toLinearMap.restrictScalars ℝ) X ε).symm
  simpa only [hmap, finiteMatrixHilbert_norm] using he

omit [NeZero d] [DecidableEq ι] in
theorem matrixSignSum_commutator (V : CMatrix d) (X : ι → CMatrix d) (ε : ι → Bool) :
    V * finiteSignSum X ε - finiteSignSum X ε * V =
      finiteSignSum (fun i => V * X i - X i * V) ε := by
  simp only [finiteSignSum, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    smul_sub, Finset.sum_sub_distrib]

theorem matrixSignSum_expect_energy (U : Fin h → UnitaryMatrix d) (X : ι → CMatrix d) :
    (𝔼 ε : ι → Bool, matrixCoordinateEnergy U (finiteSignSum X ε)) =
      ∑ i, matrixCoordinateEnergy U (X i) := by
  simp only [matrixCoordinateEnergy, matrixSignSum_commutator, ← Finset.mul_expect,
    Finset.expect_sum_comm, matrixSignSum_expect_hsNorm_sq, ← Finset.mul_sum]
  congr 1
  exact Finset.sum_comm

theorem matrixSignSum_expect_map_energy (U : Fin h → UnitaryMatrix d)
    (T : CMatrix d →ₗ[ℂ] CMatrix d) (X : ι → CMatrix d) :
    (𝔼 ε : ι → Bool, matrixCoordinateEnergy U (T (finiteSignSum X ε))) =
      ∑ i, matrixCoordinateEnergy U (T (X i)) := by
  have he (ε : ι → Bool) : T (finiteSignSum X ε) = finiteSignSum (fun i => T (X i)) ε :=
    finiteSignSum_map (T.restrictScalars ℝ) X ε
  simp only [he, matrixSignSum_expect_energy]

theorem matrixSignSum_expect_defect_sq (T : CMatrix d →ₗ[ℂ] CMatrix d) (X : ι → CMatrix d) :
    (𝔼 ε : ι → Bool, hsNorm (finiteSignSum X ε - T (finiteSignSum X ε)) ^ 2) =
      ∑ i, hsNorm (X i - T (X i)) ^ 2 := by
  have he (ε : ι → Bool) : T (finiteSignSum X ε) = finiteSignSum (fun i => T (X i)) ε :=
    finiteSignSum_map (T.restrictScalars ℝ) X ε
  simp only [he, finiteSignSum_sub, matrixSignSum_expect_hsNorm_sq]

end ThomGame.Analysis
