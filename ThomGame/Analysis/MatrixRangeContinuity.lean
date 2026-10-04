module

public import ThomGame.Analysis.MatrixPartitionTilt

/-!
# Joint continuity of actual exponential ranges

The initial support is fixed by an invertible left multiplier. The
filled Gram formula therefore proves joint continuity without making
any continuity assumption about a choice of polar factors.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped Matrix.Norms.Frobenius

variable {ι κ μ α : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
  [DecidableEq ι] [DecidableEq κ] [TopologicalSpace α]

omit [Fintype ι] [Fintype μ] [DecidableEq ι] in
theorem squareMatrix_inverse_continuous {A : α → Matrix κ κ ℂ}
    (hA : Continuous A) (hunit : ∀ s, IsUnit (A s)) :
    Continuous (fun s => (A s)⁻¹) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  obtain ⟨u, hu⟩ := hunit s
  have hi := NormedRing.inverse_continuousAt u
  rw [hu] at hi
  simpa only [Matrix.nonsing_inv_eq_ringInverse, Function.comp_def] using!
    hi.comp hA.continuousAt

omit [Fintype μ] [DecidableEq ι] in
theorem matrixRangeProjection_continuous_of_fixed_support
    {X : α → Matrix ι κ ℂ} {P : Matrix κ κ ℂ}
    (hX : Continuous X) (hP : ∀ s, matrixRealSupport (matrixRectAbs (X s)) = P) :
    Continuous (fun s => matrixRangeProjection (X s)) := by
  have hg : Continuous (fun s => (X s)ᴴ * X s + (1 - P)) := by fun_prop
  have hi := squareMatrix_inverse_continuous hg (fun s => matrixFixedGram_isUnit (hP s))
  simp_rw [matrixRangeProjection_fixed_formula (hP _)]
  fun_prop

omit [Fintype ι] [Fintype κ] [DecidableEq κ] [DecidableEq ι] in
theorem matrixProjectionParameter_continuous (E : μ → Matrix ι ι ℂ) :
    Continuous (matrixProjectionParameter E) := by
  unfold matrixProjectionParameter
  fun_prop

omit [Fintype μ] in
theorem matrixExponentialRange_joint_continuous {A : α → Matrix ι ι ℂ}
    (hA : Continuous A) (hHerm : ∀ s, Matrix.IsHermitian (A s))
    (Y : Matrix ι κ ℂ) (t : ℝ) :
    Continuous (fun s => matrixExponentialRange t (A s) Y) := by
  have hX : Continuous (fun s => matrixRealExp t (A s) * Y) := by
    simp_rw [matrixRealExp_eq_exp t (hHerm _)]
    fun_prop
  exact matrixRangeProjection_continuous_of_fixed_support hX (fun s =>
    matrix_absSupport_of_left_inverse _ _ Y (matrixRealExp_inverse t (hHerm s)))

theorem matrixPartitionRange_continuous (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (Y : Matrix ι κ ℂ) (t : ℝ) :
    Continuous (matrixPartitionRange E Y t) :=
  matrixExponentialRange_joint_continuous (matrixProjectionParameter_continuous E)
    (matrixProjectionParameter_isHermitian E hE) Y t

end ThomGame.Analysis
