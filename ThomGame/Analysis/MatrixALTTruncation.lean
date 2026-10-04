module

public import ThomGame.Analysis.MatrixRightClampMoments

/-!
# The actual fourth-moment truncation in ALT Theorem 5.2

At cutoff 2 / sqrt(a), the removed tail has at most one quarter of
the squared Hilbert norm, and the retained trace pairing is at least
one half. Dividing the clipped matrix by the cutoff gives a contraction.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra

noncomputable def matrixALTTruncation {d : Nat} (a : ℝ) (X : CMatrix d) : CMatrix d :=
  cstarRightNormClamp (2 / Real.sqrt a) X

noncomputable def matrixALTTruncationContraction {d : Nat} (a : ℝ) (X : CMatrix d) : CMatrix d :=
  ((Real.sqrt a / 2 : ℝ) : ℂ) • matrixALTTruncation a X

theorem matrixALTTruncation_cutoff (a : ℝ) (ha : 0 < a) :
    0 < 2 / Real.sqrt a ∧ a * (2 / Real.sqrt a) ^ 2 = 4 := by
  have hs := Real.sqrt_pos.mpr ha
  refine ⟨div_pos (by norm_num) hs, ?_⟩
  rw [div_pow, Real.sq_sqrt ha.le]
  field_simp
  ring

variable {d : Nat}

theorem matrixALTTruncation_tail (a : ℝ) (ha : 0 < a) (X : CMatrix d)
    (hmoment : a * hsNorm (star X * X) ^ 2 ≤ hsNorm X ^ 2) :
    hsNorm (X - matrixALTTruncation a X) ^ 2 ≤ hsNorm X ^ 2 / 4 := by
  obtain ⟨hR, he⟩ := matrixALTTruncation_cutoff a ha
  have ht := mul_le_mul_of_nonneg_left (matrixRightNormClamp_tail_fourth _ hR X) ha.le
  change a * ((2 / Real.sqrt a) ^ 2 * hsNorm (X - matrixALTTruncation a X) ^ 2) ≤ _ at ht
  rw [← mul_assoc, he] at ht
  linarith

theorem matrixALTTruncation_pairing [NeZero d] (a : ℝ) (ha : 0 < a) (X : CMatrix d)
    (hmoment : a * hsNorm (star X * X) ^ 2 ≤ hsNorm X ^ 2) :
    hsNorm X ^ 2 / 2 ≤ (normalizedTrace (star X * matrixALTTruncation a X)).re := by
  have ht := matrixALTTruncation_tail a ha X hmoment
  have hn := hsNorm_nonneg X
  have he := hsNorm_nonneg (X - matrixALTTruncation a X)
  have hb : hsNorm (X - matrixALTTruncation a X) ≤ hsNorm X / 2 := by nlinarith
  have hc := (le_abs_self _).trans (abs_normalizedTrace_pairing_re_le X (X - matrixALTTruncation a X))
  have hm := mul_le_mul_of_nonneg_left hb hn
  rw [mul_sub, normalizedTrace_sub, normalizedTrace_gram, Complex.sub_re, Complex.ofReal_re] at hc
  nlinarith

theorem matrixALTTruncationContraction_norm (a : ℝ) (ha : 0 < a) (X : CMatrix d) :
    matrixOpNorm (matrixALTTruncationContraction a X) ≤ 1 := by
  have hs := Real.sqrt_pos.mpr ha
  have hb := cstarRightNormClamp_norm_le (2 / Real.sqrt a) (matrixALTTruncation_cutoff a ha).1 X
  change ‖((Real.sqrt a / 2 : ℝ) : ℂ) • matrixALTTruncation a X‖ ≤ 1
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hs (by norm_num))]
  calc
    _ ≤ (Real.sqrt a / 2) * (2 / Real.sqrt a) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 1 := by field_simp

theorem matrixALTTruncationContraction_rectangle (a : ℝ) (P Q X : CMatrix d)
    (hQ : IsSelfAdjoint Q) (hl : P * X = X) (hr : X * Q = X) :
    P * matrixALTTruncationContraction a X = matrixALTTruncationContraction a X ∧
      matrixALTTruncationContraction a X * Q = matrixALTTruncationContraction a X := by
  obtain ⟨hl', hr'⟩ := matrixRightNormClamp_rectangle (2 / Real.sqrt a) P Q X hQ hl hr
  simp only [matrixALTTruncationContraction, matrixALTTruncation, mul_smul_comm, smul_mul_assoc, hl', hr',
    and_self]

end ThomGame.Analysis
