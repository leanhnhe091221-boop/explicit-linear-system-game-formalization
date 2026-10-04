module

public import ThomGame.Analysis.MatrixOrthogonalFamilyBounds

/-!
# The two bad projection families in ALT Theorem 2.4

Distance-bad and energy-bad are predicates on actual nonzero matrix
projections and actual Markov powers. Uniform sign bounds control
the total normalized trace of every finite orthogonal bad family.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator

variable {d h : Nat}

def MatrixDistanceBad (U : Fin h → UnitaryMatrix d) (κ α : ℝ) (k : Nat) (P : CMatrix d) : Prop :=
  IsStarProjection P ∧ P ≠ 0 ∧ α * (normalizedTrace P).re ≤ matrixCoordinateEnergy U P ∧
    2 * (Real.sqrt κ)⁻¹ * Real.sqrt (matrixCoordinateEnergy U P) <
      hsNorm (P - (matrixLazyMarkov U ^ k) P)

def MatrixEnergyBad (U : Fin h → UnitaryMatrix d) (α : ℝ) (k : Nat) (P : CMatrix d) : Prop :=
  IsStarProjection P ∧ P ≠ 0 ∧ α ^ 2 * (normalizedTrace P).re / 36 <
    matrixCoordinateEnergy U ((matrixLazyMarkov U ^ k) P)

variable [NeZero d] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrixMarkovOrthogonalFamily_bad_energy_bound (U : Fin h → UnitaryMatrix d)
    (κ : ℝ) (hκ : 0 < κ) (k : Nat) (P : ι → CMatrix d)
    (hP : ∀ i, IsStarProjection (P i)) (horth : Pairwise (fun i j => P i * P j = 0))
    (hbad : ∀ i, 2 * (Real.sqrt κ)⁻¹ * Real.sqrt (matrixCoordinateEnergy U (P i)) ≤
      hsNorm (P i - (matrixLazyMarkov U ^ k) (P i))) :
    (∑ i, matrixCoordinateEnergy U (P i)) ≤ κ * matrixMarkovDefectBound U κ k ^ 2 := by
  have hsE : 0 ≤ ∑ i, matrixCoordinateEnergy U (P i) :=
    Finset.sum_nonneg fun i _ => matrixCoordinateEnergy_nonneg U _
  have hlow : (2 * (Real.sqrt κ)⁻¹ * Real.sqrt (∑ i, matrixCoordinateEnergy U (P i))) ^ 2 ≤
      ∑ i, hsNorm (P i - (matrixLazyMarkov U ^ k) (P i)) ^ 2 := by
    calc
      _ = ∑ i, (2 * (Real.sqrt κ)⁻¹ * Real.sqrt (matrixCoordinateEnergy U (P i))) ^ 2 := by
        simp only [mul_pow, Real.sq_sqrt hsE, Real.sq_sqrt (matrixCoordinateEnergy_nonneg U _)]
        rw [Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum fun i _ =>
        (sq_le_sq₀ (by positivity) (hsNorm_nonneg _)).2 (hbad i)
  have hlowRoot := Real.le_sqrt_of_sq_le hlow
  have hupper := matrixMarkovOrthogonalFamily_distance_bound U κ k P hP horth
  have hmain : (Real.sqrt κ)⁻¹ * Real.sqrt (∑ i, matrixCoordinateEnergy U (P i)) ≤
      matrixMarkovDefectBound U κ k := by linarith
  have hsκ : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hs : Real.sqrt (∑ i, matrixCoordinateEnergy U (P i)) ≤
      matrixMarkovDefectBound U κ k * Real.sqrt κ := by
    apply (div_le_iff₀ hsκ).mp
    simpa only [div_eq_inv_mul] using hmain
  have hs₂ := (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg
    (matrixMarkovDefectBound_nonneg U κ k) (Real.sqrt_nonneg κ))).2 hs
  simpa only [Real.sq_sqrt hsE, mul_pow, Real.sq_sqrt hκ.le, mul_comm] using hs₂

theorem matrixDistanceBad_family_trace_bound (U : Fin h → UnitaryMatrix d)
    (κ α : ℝ) (hκ : 0 < κ) (hα : 0 < α) (k : Nat) (P : ι → CMatrix d)
    (hbad : ∀ i, MatrixDistanceBad U κ α k (P i))
    (horth : Pairwise (fun i j => P i * P j = 0)) :
    (∑ i, (normalizedTrace (P i)).re) ≤ κ * matrixMarkovDefectBound U κ k ^ 2 / α := by
  have he := matrixMarkovOrthogonalFamily_bad_energy_bound U κ hκ k P
    (fun i => (hbad i).1) horth (fun i => (hbad i).2.2.2.le)
  have ht : α * (∑ i, (normalizedTrace (P i)).re) ≤ ∑ i, matrixCoordinateEnergy U (P i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => (hbad i).2.2.1
  apply (le_div_iff₀ hα).2
  linarith

theorem matrixEnergyBad_family_trace_bound (U : Fin h → UnitaryMatrix d)
    (κ α : ℝ) (hα : 0 < α) (k : Nat) (P : ι → CMatrix d)
    (hbad : ∀ i, MatrixEnergyBad U α k (P i))
    (horth : Pairwise (fun i j => P i * P j = 0)) :
    (∑ i, (normalizedTrace (P i)).re) ≤ 36 * matrixMarkovDefectBound U κ k ^ 2 / α ^ 2 := by
  have he := matrixMarkovOrthogonalFamily_energy_bound U κ k P (fun i => (hbad i).1) horth
  have ht : α ^ 2 * (∑ i, (normalizedTrace (P i)).re) ≤
      36 * ∑ i, matrixCoordinateEnergy U ((matrixLazyMarkov U ^ k) (P i)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by linarith [(hbad i).2.2.le]
  apply (le_div_iff₀ (sq_pos_of_pos hα)).2
  nlinarith

end ThomGame.Analysis
