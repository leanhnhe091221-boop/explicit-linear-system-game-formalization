module

public import ThomGame.Analysis.FiniteMatrixHilbert

/-!
# Positive rescaling to a prescribed normalized Hilbert mass

The actual scalar is retained, so orthogonality and eigenvector equations
can be transported through the normalization.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d]

theorem exists_matrixHS_positive_rescaling (X : CMatrix d) (hX : X ≠ 0) (M : ℝ) (hM : 0 < M) :
    ∃ a : ℝ, 0 < a ∧ hsNorm ((a : ℂ) • X) ^ 2 = M := by
  have hn : 0 < hsNorm X := lt_of_le_of_ne (hsNorm_nonneg X) (Ne.symm (by
    intro hz
    exact hX ((hsNorm_eq_zero_iff X).mp hz)))
  let a := Real.sqrt M / hsNorm X
  have ha : 0 < a := div_pos (Real.sqrt_pos.mpr hM) hn
  refine ⟨a, ha, ?_⟩
  rw [hsNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  change (Real.sqrt M / hsNorm X * hsNorm X) ^ 2 = M
  rw [div_mul_cancel₀ _ hn.ne', Real.sq_sqrt hM.le]

omit [NeZero d] in
theorem normalizedTrace_pairing_smul (a b : ℂ) (X Y : CMatrix d) :
    normalizedTrace (star (a • X) * (b • Y)) = star a * b * normalizedTrace (star X * Y) := by
  rw [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul, normalizedTrace_smul]

end ThomGame.Analysis
