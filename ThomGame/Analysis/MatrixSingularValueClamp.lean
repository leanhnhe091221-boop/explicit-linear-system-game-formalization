module

public import ThomGame.Analysis.MatrixPolarUnitary

/-!
# Clipping the actual singular values of a rectangular matrix at one

The multiplier (max(t,1)) inverse is defined at zero as well. Its
product with X has absolute value min(|X|,1), with no kernel assumption.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem real_mul_clampMultiplier (t : ℝ) :
    t * (max t 1)⁻¹ = min t 1 := by
  by_cases h : t ≤ 1
  · simp [max_eq_right h, min_eq_left h]
  · have hp : 0 < t := lt_of_lt_of_le zero_lt_one (le_of_not_ge h)
    simp [max_eq_left (le_of_not_ge h), min_eq_right (le_of_not_ge h), ne_of_gt hp]

theorem realNormClamp_eq_mul_clampMultiplier (t : ℝ) :
    realNormClamp 1 t = t * (max |t| 1)⁻¹ := by
  by_cases hp : 0 ≤ t
  · rw [abs_of_nonneg hp, real_mul_clampMultiplier]
    simpa only [realNormClamp, min_comm] using
      max_eq_right (le_trans (by norm_num : (-1 : ℝ) ≤ 0) (le_min hp zero_le_one))
  · have hn : t ≤ 0 := le_of_not_ge hp
    have he := real_mul_clampMultiplier (-t)
    rw [abs_of_nonpos hn]
    by_cases h : -t ≤ 1
    · have ht : -1 ≤ t := by linarith
      simp only [realNormClamp, max_eq_right h, inv_one, mul_one,
        min_eq_right (hn.trans zero_le_one), max_eq_right ht]
    · have ht : t ≤ -1 := by linarith
      rw [min_eq_right (le_of_not_ge h), neg_mul] at he
      have hv : t * (max (-t) 1)⁻¹ = -1 := by linarith
      rw [hv]
      simp only [realNormClamp, min_eq_right (hn.trans zero_le_one), max_eq_left ht]

omit [DecidableEq ι] in
noncomputable def matrixRectClamp (X : Matrix ι κ ℂ) : Matrix ι κ ℂ :=
  X * cfc (fun t : ℝ => (max t 1)⁻¹) (matrixRectAbs X)

omit [DecidableEq ι] in
theorem matrixRectAbs_mul_clampMultiplier (X : Matrix ι κ ℂ) :
    matrixRectAbs X * cfc (fun t : ℝ => (max t 1)⁻¹) (matrixRectAbs X) =
      cfc (fun t : ℝ => min t 1) (matrixRectAbs X) := by
  have hid : cfc (fun t : ℝ => t) (matrixRectAbs X) = matrixRectAbs X :=
    cfc_id' ℝ _ (matrixRectAbs_nonneg X).isSelfAdjoint
  conv_lhs => lhs; rw [← hid]
  rw [← cfc_mul _ _ _ ((matrixRectAbs X).finite_real_spectrum.continuousOn _)
    ((matrixRectAbs X).finite_real_spectrum.continuousOn _)]
  apply cfc_congr
  intro t _
  exact real_mul_clampMultiplier t

omit [DecidableEq ι] in
theorem matrixRectClamp_eq_polar_min (X : Matrix ι κ ℂ) :
    matrixRectClamp X = matrixRectPolar X * cfc (fun t : ℝ => min t 1) (matrixRectAbs X) := by
  rw [← matrixRectAbs_mul_clampMultiplier, ← Matrix.mul_assoc, matrixRectPolar_mul_abs]
  rfl

omit [DecidableEq ι] in
theorem matrixRectClamp_gram (X : Matrix ι κ ℂ) :
    (matrixRectClamp X)ᴴ * matrixRectClamp X =
      cfc (fun t : ℝ => min t 1) (matrixRectAbs X) *
        cfc (fun t : ℝ => min t 1) (matrixRectAbs X) := by
  let A := matrixRectAbs X
  let G := cfc (fun t : ℝ => (max t 1)⁻¹) A
  have hGs : IsSelfAdjoint G := cfc_predicate _ A
  have hG : Gᴴ = G := hGs.isHermitian.eq
  have hAG : A * G = cfc (fun t : ℝ => min t 1) A := matrixRectAbs_mul_clampMultiplier X
  have hGA : G * A = cfc (fun t : ℝ => min t 1) A := by
    have hid : cfc (fun t : ℝ => t) A = A := cfc_id' ℝ A (matrixRectAbs_nonneg X).isSelfAdjoint
    rw [← hAG]
    exact hid ▸ (cfc_commute_cfc (fun t : ℝ => (max t 1)⁻¹) (fun t : ℝ => t) A).eq
  change (X * G)ᴴ * (X * G) = _
  rw [Matrix.conjTranspose_mul, hG]
  calc
    _ = G * (Xᴴ * X) * G := by simp only [Matrix.mul_assoc]
    _ = (G * A) * (A * G) := by rw [← matrixRectAbs_mul_self X]; simp only [A, Matrix.mul_assoc]
    _ = _ := by rw [hGA, hAG]

omit [DecidableEq ι] in
theorem matrixRectClamp_abs (X : Matrix ι κ ℂ) :
    matrixRectAbs (matrixRectClamp X) = cfc (fun t : ℝ => min t 1) (matrixRectAbs X) := by
  apply CFC.sqrt_unique
  · exact (matrixRectClamp_gram X).symm
  · apply cfc_nonneg
    intro t ht
    exact le_min (spectrum_nonneg_of_nonneg (matrixRectAbs_nonneg X) ht) zero_le_one

omit [DecidableEq ι] in
theorem matrixRectClamp_abs_le_one (X : Matrix ι κ ℂ) :
    matrixRectAbs (matrixRectClamp X) ≤ 1 := by
  rw [matrixRectClamp_abs]
  apply (cfc_le_one_iff _ _ ((matrixRectAbs X).finite_real_spectrum.continuousOn _)
    (matrixRectAbs_nonneg X).isSelfAdjoint).mpr
  intro t _
  exact min_le_right _ _

theorem matrixRectClamp_conjTranspose (X : Matrix ι κ ℂ) :
    matrixRectClamp Xᴴ = (matrixRectClamp X)ᴴ := by
  have he := matrix_cfc_intertwine (matrixRectAbs_isHermitian Xᴴ) (matrixRectAbs_isHermitian X)
    (fun t : ℝ => (max t 1)⁻¹) X (matrixRectAbs_intertwine X)
  have hsa : IsSelfAdjoint (cfc (fun t : ℝ => (max t 1)⁻¹) (matrixRectAbs X)) := cfc_predicate _ _
  have hsa' : IsSelfAdjoint (cfc (fun t : ℝ => (max t 1)⁻¹) (matrixRectAbs Xᴴ)) := cfc_predicate _ _
  have hs := hsa.isHermitian.eq
  have hs' := hsa'.isHermitian.eq
  simpa only [matrixRectClamp, Matrix.conjTranspose_mul, hs, hs'] using
    congrArg Matrix.conjTranspose he

theorem matrixSelfAdjointDilation_clamp (X : Matrix ι κ ℂ) :
    cfc (realNormClamp 1) (matrixSelfAdjointDilation X) =
      matrixSelfAdjointDilation (matrixRectClamp X) := by
  let D := matrixSelfAdjointDilation X
  have hD := matrixSelfAdjointDilation_isHermitian X
  have hid : cfc (fun t : ℝ => t) D = D := cfc_id' ℝ D hD.isSelfAdjoint
  have he : cfc (realNormClamp 1) D = D * cfc (fun t : ℝ => (max t 1)⁻¹) (cfc (abs : ℝ → ℝ) D) := by
    rw [← cfc_comp' (fun t : ℝ => (max t 1)⁻¹) abs D
      ((D.finite_real_spectrum.image abs).continuousOn _) (D.finite_real_spectrum.continuousOn _) hD.isSelfAdjoint]
    conv_rhs => lhs; rw [← hid]
    rw [← cfc_mul _ _ D (D.finite_real_spectrum.continuousOn _)
      (D.finite_real_spectrum.continuousOn _)]
    apply cfc_congr
    intro t _
    exact realNormClamp_eq_mul_clampMultiplier t
  rw [he, matrixSelfAdjointDilation_cfc_abs,
    matrix_cfc_blockDiagonal (matrixRectAbs_isHermitian Xᴴ) (matrixRectAbs_isHermitian X)]
  simp only [D, matrixSelfAdjointDilation, Matrix.fromBlocks_multiply, Matrix.zero_mul,
    Matrix.mul_zero, zero_add, add_zero]
  change Matrix.fromBlocks 0 (matrixRectClamp X) (matrixRectClamp Xᴴ) 0 = _
  rw [matrixRectClamp_conjTranspose]

end ThomGame.Analysis
