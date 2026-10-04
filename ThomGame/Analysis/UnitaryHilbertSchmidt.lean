module

public import ThomGame.Analysis.NormalizedHilbertSchmidt

/-!
# Dimension-independent Hilbert--Schmidt estimates on actual unitaries

Left and right unitary multiplication preserve the normalized norm.
Distance to the identity is symmetric under inversion, invariant under
conjugation, subadditive on products and bounded by two in every positive
dimension. These estimates will control relation errors and their limits.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix

variable {d : Nat}

theorem hsNorm_unitary_mul (U : UnitaryMatrix d) (A : CMatrix d) :
    hsNorm (U.val * A) = hsNorm A := by
  have hU : U.valᴴ * U.val = 1 := U.prop.1
  have he : (U.val * A)ᴴ * (U.val * A) = Aᴴ * A := by
    rw [conjTranspose_mul, mul_assoc, ← mul_assoc U.valᴴ U.val A, hU, one_mul]
  rw [hsNorm_eq_sqrt_trace, he, ← hsNorm_eq_sqrt_trace]

theorem hsNorm_mul_unitary (A : CMatrix d) (U : UnitaryMatrix d) :
    hsNorm (A * U.val) = hsNorm A := by
  rw [← hsNorm_conjTranspose (A * U.val), conjTranspose_mul]
  change hsNorm ((U⁻¹).val * Aᴴ) = _
  rw [hsNorm_unitary_mul, hsNorm_conjTranspose]

noncomputable def unitaryDist (U V : UnitaryMatrix d) : ℝ := hsNorm (U.val - V.val)

noncomputable def unitaryLength (U : UnitaryMatrix d) : ℝ := unitaryDist U 1

theorem unitaryDist_nonneg (U V : UnitaryMatrix d) : 0 ≤ unitaryDist U V := hsNorm_nonneg _

theorem unitaryDist_comm (U V : UnitaryMatrix d) : unitaryDist U V = unitaryDist V U :=
  hsNorm_sub_comm _ _

@[simp] theorem unitaryDist_self (U : UnitaryMatrix d) : unitaryDist U U = 0 := by
  simp [unitaryDist]

theorem unitaryDist_triangle (U V W : UnitaryMatrix d) :
    unitaryDist U W ≤ unitaryDist U V + unitaryDist V W := by
  have h := hsNorm_add_le (U.val - V.val) (V.val - W.val)
  simpa only [unitaryDist, sub_add_sub_cancel] using h

theorem unitaryDist_mul_left (U V W : UnitaryMatrix d) :
    unitaryDist (U * V) (U * W) = unitaryDist V W := by
  change hsNorm (U.val * V.val - U.val * W.val) = _
  rw [← mul_sub, hsNorm_unitary_mul]
  rfl

theorem unitaryDist_mul_right (U V W : UnitaryMatrix d) :
    unitaryDist (U * W) (V * W) = unitaryDist U V := by
  change hsNorm (U.val * W.val - V.val * W.val) = _
  rw [← sub_mul, hsNorm_mul_unitary]
  rfl

theorem unitaryLength_nonneg (U : UnitaryMatrix d) : 0 ≤ unitaryLength U := unitaryDist_nonneg _ _

@[simp] theorem unitaryLength_one : unitaryLength (1 : UnitaryMatrix d) = 0 := unitaryDist_self _

@[simp] theorem unitaryLength_inv (U : UnitaryMatrix d) : unitaryLength U⁻¹ = unitaryLength U := by
  have h := unitaryDist_mul_left U U⁻¹ 1
  simpa only [unitaryLength, mul_inv_cancel, mul_one, unitaryDist_comm 1 U] using h.symm

theorem unitaryLength_mul_le (U V : UnitaryMatrix d) :
    unitaryLength (U * V) ≤ unitaryLength U + unitaryLength V := by
  have h := unitaryDist_triangle (U * V) (1 * V) 1
  rw [unitaryDist_mul_right, one_mul] at h
  exact h

@[simp] theorem unitaryLength_conj (U V : UnitaryMatrix d) :
    unitaryLength (U * V * U⁻¹) = unitaryLength V := by
  unfold unitaryLength
  rw [← mul_inv_cancel U, unitaryDist_mul_right, mul_inv_cancel]
  simpa only [mul_one] using unitaryDist_mul_left U V 1

theorem unitaryDist_eq_length (U V : UnitaryMatrix d) :
    unitaryDist U V = unitaryLength (U * V⁻¹) := by
  have h := unitaryDist_mul_right U V V⁻¹
  simpa only [unitaryLength, mul_inv_cancel] using h.symm

variable [NeZero d]

@[simp] theorem unitaryDist_eq_zero_iff (U V : UnitaryMatrix d) : unitaryDist U V = 0 ↔ U = V := by
  rw [unitaryDist, hsNorm_sub_eq_zero_iff]
  exact Subtype.val_inj

@[simp] theorem unitaryLength_eq_zero_iff (U : UnitaryMatrix d) : unitaryLength U = 0 ↔ U = 1 :=
  unitaryDist_eq_zero_iff _ _

@[simp] theorem hsNorm_unitary (U : UnitaryMatrix d) : hsNorm U.val = 1 := by
  have h := hsNorm_unitary_mul U 1
  simpa only [mul_one, hsNorm_one] using h

theorem unitaryDist_le_two (U V : UnitaryMatrix d) : unitaryDist U V ≤ 2 := by
  have h := hsNorm_add_le U.val (-V.val)
  simpa only [← sub_eq_add_neg, hsNorm_neg, hsNorm_unitary, unitaryDist, one_add_one_eq_two] using h

theorem unitaryLength_le_two (U : UnitaryMatrix d) : unitaryLength U ≤ 2 := unitaryDist_le_two _ _

theorem unitaryLength_neg_one : unitaryLength (-1 : UnitaryMatrix d) = 2 := by
  change hsNorm (-(1 : CMatrix d) - 1) = 2
  have h : -(1 : CMatrix d) - 1 = (-2 : ℂ) • (1 : CMatrix d) := by
    simp [neg_smul, two_smul, sub_eq_add_neg]
  rw [h, hsNorm_smul, hsNorm_one]
  norm_num

end ThomGame.Analysis
