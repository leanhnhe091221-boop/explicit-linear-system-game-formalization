module

public import ThomGame.Analysis.MatrixAlgebraicIntertwinerMultiplicity

/-!
# Weighted multiplicity distance controlled by the rank of an intertwiner

The exact identity is the weighted form of |q'-q| = q+q'-2 min(q,q').
All multiplicities are ranks of the actual representation matrices.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {d m n : Nat} (A : StarSubalgebra ℂ (CMatrix d))
    (S : MatrixSubalgebraAlgebraicBlocks A)
    (ρ : A →ₐ[ℂ] CMatrix n) (σ : A →ₐ[ℂ] CMatrix m)

noncomputable def matrixAlgebraicMultiplicityDistance : ℝ :=
  ∑ i, (S.size i : ℝ) * |(matrixAlgebraicRepresentationMultiplicity A S σ i : ℝ) -
    (matrixAlgebraicRepresentationMultiplicity A S ρ i : ℝ)|

theorem matrixAlgebraicMultiplicityDistance_nonneg : 0 ≤ matrixAlgebraicMultiplicityDistance A S ρ σ :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))

theorem matrixAlgebraicMultiplicityDistance_eq :
    matrixAlgebraicMultiplicityDistance A S ρ σ = (n : ℝ) + m -
      2 * ((∑ i, S.size i * min (matrixAlgebraicRepresentationMultiplicity A S ρ i)
        (matrixAlgebraicRepresentationMultiplicity A S σ i) : Nat) : ℝ) := by
  have hpoint (i : Fin S.count) :
      (S.size i : ℝ) * |(matrixAlgebraicRepresentationMultiplicity A S σ i : ℝ) -
        (matrixAlgebraicRepresentationMultiplicity A S ρ i : ℝ)| =
      (S.size i : ℝ) * (matrixAlgebraicRepresentationMultiplicity A S ρ i : ℝ) +
        (S.size i : ℝ) * (matrixAlgebraicRepresentationMultiplicity A S σ i : ℝ) -
        2 * ((S.size i * min (matrixAlgebraicRepresentationMultiplicity A S ρ i)
          (matrixAlgebraicRepresentationMultiplicity A S σ i) : Nat) : ℝ) := by
    simp only [Nat.cast_mul, Nat.cast_min]
    by_cases h : (matrixAlgebraicRepresentationMultiplicity A S ρ i : ℝ) ≤
        (matrixAlgebraicRepresentationMultiplicity A S σ i : ℝ)
    · rw [abs_of_nonneg (sub_nonneg.mpr h), min_eq_left h]
      ring
    · have h' := le_of_lt (lt_of_not_ge h)
      rw [abs_of_nonpos (sub_nonpos.mpr h'), min_eq_right h']
      ring
  have hn : (∑ i, (S.size i : ℝ) * (matrixAlgebraicRepresentationMultiplicity A S ρ i : ℝ)) = n := by
    exact_mod_cast (matrixAlgebraicRepresentation_dimension A S ρ).symm
  have hm : (∑ i, (S.size i : ℝ) * (matrixAlgebraicRepresentationMultiplicity A S σ i : ℝ)) = m := by
    exact_mod_cast (matrixAlgebraicRepresentation_dimension A S σ).symm
  unfold matrixAlgebraicMultiplicityDistance
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hn, hm, Nat.cast_sum]

theorem matrixAlgebraicMultiplicityDistance_le_intertwiner
    (T : Matrix (Fin m) (Fin n) ℂ) (hT : ∀ X : A, T * ρ X = σ X * T) :
    matrixAlgebraicMultiplicityDistance A S ρ σ ≤ (n : ℝ) + m - 2 * T.rank := by
  rw [matrixAlgebraicMultiplicityDistance_eq]
  have h : (T.rank : ℝ) ≤
      ((∑ i, S.size i * min (matrixAlgebraicRepresentationMultiplicity A S ρ i)
        (matrixAlgebraicRepresentationMultiplicity A S σ i) : Nat) : ℝ) := by
    exact_mod_cast matrixAlgebraicIntertwiner_rank_le A S ρ σ T hT
  linarith

end ThomGame.Analysis
