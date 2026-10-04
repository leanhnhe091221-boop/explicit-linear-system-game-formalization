module

public import ThomGame.Analysis.MatrixReducingFamilyEnergy

/-!
# Energy of an arbitrary orthogonal projection family

The energy of the sum is at most the sum of the energies, even when
the original unitaries do not reduce any of the projections. Completing
the family by its complement costs at most a factor two.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι μ : Type*} [Fintype ι] [Fintype μ] [DecidableEq ι]

omit [DecidableEq ι] in
theorem rectHSNorm_projection_sum_mul_sq (r : Nat) (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (X : Matrix ι ι ℂ) :
    rectHSNorm r ((∑ i, E i) * X) ^ 2 = ∑ i, rectHSNorm r (E i * X) ^ 2 := by
  rw [Matrix.sum_mul]
  exact rectHSNorm_corner_sum_sq r E _ hE horth (fun i => by
    rw [← Matrix.mul_assoc, (hE i).isIdempotentElem.eq])

theorem rectHSNorm_mul_projection_sum_sq (r : Nat) (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (X : Matrix ι ι ℂ) :
    rectHSNorm r (X * (∑ i, E i)) ^ 2 = ∑ i, rectHSNorm r (X * E i) ^ 2 := by
  have he := rectHSNorm_projection_sum_mul_sq r E hE horth Xᴴ
  have hstar (i : μ) : E i * Xᴴ = (X * E i)ᴴ := by
    rw [Matrix.conjTranspose_mul, (hE i).isSelfAdjoint.isHermitian.eq]
  have hsumstar : (∑ i, E i) * Xᴴ = (X * (∑ i, E i))ᴴ := by
    rw [Matrix.conjTranspose_mul, (matrixProjection_sum E hE horth).isSelfAdjoint.isHermitian.eq]
  simpa only [hstar, hsumstar, rectHSNorm_conjTranspose] using he

theorem rectHSNorm_projection_sum_commutator_le (r : Nat) (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (A : Matrix ι ι ℂ) :
    rectHSNorm r (A * (∑ i, E i) - (∑ i, E i) * A) ^ 2 ≤
      ∑ i, rectHSNorm r (A * E i - E i * A) ^ 2 := by
  let S := ∑ i, E i
  let T := 1 - S
  have hS : IsStarProjection S := matrixProjection_sum E hE horth
  have hT : IsStarProjection T := hS.one_sub
  have hTe (i : μ) : T * E i = 0 := by
    change (1 - ∑ j, E j) * E i = 0
    rw [Matrix.sub_mul, Matrix.one_mul,
      matrixCorner_sum_block_right E E horth (fun j => (hE j).isIdempotentElem.eq), sub_self]
  have heT (i : μ) : E i * T = 0 := by
    simpa only [Matrix.conjTranspose_mul, hT.isSelfAdjoint.isHermitian.eq,
      (hE i).isSelfAdjoint.isHermitian.eq, Matrix.conjTranspose_zero] using
        congrArg Matrix.conjTranspose (hTe i)
  have hin (i : μ) : rectHSNorm r (T * A * E i) ^ 2 ≤
      rectHSNorm r ((1 - E i) * A * E i) ^ 2 := by
    have he := rectHSNorm_projection_mul_sq_le r hT ((1 - E i) * A * E i)
    simpa only [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, hTe, sub_zero] using he
  have hout (i : μ) : rectHSNorm r (E i * A * T) ^ 2 ≤
      rectHSNorm r (E i * A * (1 - E i)) ^ 2 := by
    have he := rectHSNorm_mul_projection_sq_le r hT (E i * A * (1 - E i))
    simpa only [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, heT, sub_zero] using he
  rw [rectHSNorm_projection_commutator_cut r A hS]
  change rectHSNorm r (T * A * S) ^ 2 + rectHSNorm r (S * A * T) ^ 2 ≤ _
  rw [rectHSNorm_mul_projection_sum_sq r E hE horth,
    Matrix.mul_assoc S A T, rectHSNorm_projection_sum_mul_sq r E hE horth, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [rectHSNorm_projection_commutator_cut r A (hE i)]
  simpa only [Matrix.mul_assoc] using add_le_add (hin i) (hout i)

theorem matrixCoordinateEnergy_orthogonal_sum_le {d h : Nat} (U : Fin h → UnitaryMatrix d)
    (E : μ → CMatrix d) (hE : ∀ i, IsStarProjection (E i))
    (horth : Pairwise (fun i j => E i * E j = 0)) :
    matrixCoordinateEnergy U (∑ i, E i) ≤ ∑ i, matrixCoordinateEnergy U (E i) := by
  have hj (j : Fin h) := rectHSNorm_projection_sum_commutator_le d E hE horth (U j).val
  simp only [rectHSNorm_eq_hsNorm] at hj
  have he := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := Finset.univ) fun j _ => hj j)
    (lazyMarkovWeight_nonneg h)
  simp only [matrixCoordinateEnergy, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  exact he

theorem matrixCoordinateEnergy_orthogonal_completion_le {d h : Nat} (U : Fin h → UnitaryMatrix d)
    (E : μ → CMatrix d) (hE : ∀ i, IsStarProjection (E i))
    (horth : Pairwise (fun i j => E i * E j = 0)) :
    (∑ i, matrixCoordinateEnergy U (matrixProjectionCompletion E i)) ≤
      2 * ∑ i, matrixCoordinateEnergy U (E i) := by
  rw [Fintype.sum_option]
  simp only [matrixProjectionCompletion_none, matrixProjectionCompletion_some]
  rw [matrixCoordinateEnergy_reducing_sub U (fun j => Commute.one_left (U j).val)]
  have he := matrixCoordinateEnergy_orthogonal_sum_le U E hE horth
  linarith only [he]

end ThomGame.Analysis
