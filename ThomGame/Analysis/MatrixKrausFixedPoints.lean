module

public import ThomGame.Analysis.MatrixChannelEnergy

/-!
# Fixed matrices of an actual trace-preserving unital Kraus map

The proved energy identity identifies fixed points with matrices
commuting with every Kraus coefficient. No fixed-point algebra is assumed.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d] {ι : Type*} [Fintype ι]

theorem matrixKraus_fixed_iff_commute (F : CMatrix d →ₗ[ℂ] CMatrix d) (a : ι → CMatrix d)
    (hrep : ∀ X, F X = ∑ k, star (a k) * X * a k) (hF : F 1 = 1)
    (htrace : ∀ X, normalizedTrace (F X) = normalizedTrace X) (X : CMatrix d) :
    F X = X ↔ ∀ k, a k * X = X * a k := by
  constructor
  · intro hX k
    have he := matrixChannelEnergy_kraus F a hrep hF htrace X
    have hz : matrixChannelEnergy F X = 0 := by
      rw [matrixChannelEnergy, hX, normalizedTrace_gram, Complex.ofReal_re, sub_self]
    rw [hz, mul_zero] at he
    have hle : hsNorm (a k * X - X * a k) ^ 2 ≤ ∑ j, hsNorm (a j * X - X * a j) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (hsNorm (a j * X - X * a j))) (Finset.mem_univ k)
    rw [he] at hle
    exact (hsNorm_sub_eq_zero_iff _ _).mp (sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg _)))
  · intro hX
    have hunit : ∑ k, star (a k) * a k = 1 := by
      simpa only [mul_one] using (hrep 1).symm.trans hF
    have ht (k : ι) : star (a k) * X * a k = (star (a k) * a k) * X := by
      rw [mul_assoc, ← hX k, ← mul_assoc]
    rw [hrep]
    simp_rw [ht]
    rw [← Finset.sum_mul, hunit, one_mul]

end ThomGame.Analysis
