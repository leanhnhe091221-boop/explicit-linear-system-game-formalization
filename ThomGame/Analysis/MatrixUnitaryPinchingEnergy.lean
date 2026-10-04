module

public import ThomGame.Analysis.MatrixPinchingPythagoras
public import ThomGame.Analysis.MatrixIntertwiningEnergy

/-!
# Unitary pinching defects and exact boundary-energy identities
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι μ : Type*} [Fintype ι] [Fintype μ] [DecidableEq ι]

omit [Fintype μ] in
theorem matrixUnitary_projection_gram (U : Matrix.unitaryGroup ι ℂ) {q : Matrix ι ι ℂ}
    (hq : IsStarProjection q) : (U.val * q)ᴴ * (U.val * q) = q := by
  have hu : U.valᴴ * U.val = 1 := U.prop.1
  rw [Matrix.conjTranspose_mul, hq.isSelfAdjoint.isHermitian.eq]
  calc
    _ = q * (U.valᴴ * U.val) * q := by simp only [Matrix.mul_assoc]
    _ = q := by rw [hu, Matrix.mul_one, hq.isIdempotentElem.eq]

omit [Fintype μ] in
theorem matrixUnitary_compression_gram_le (U : Matrix.unitaryGroup ι ℂ) {q : Matrix ι ι ℂ}
    (hq : IsStarProjection q) : (q * U.val * q)ᴴ * (q * U.val * q) ≤ q := by
  have he := matrixProjection_compression_gram_le hq (U.val * q)
  simpa only [← Matrix.mul_assoc q U.val q, matrixUnitary_projection_gram U hq] using he

omit [Fintype μ] in
theorem rectHSNorm_unitary_projection_commutator_sq (r : Nat) (U : Matrix.unitaryGroup ι ℂ)
    {q : Matrix ι ι ℂ} (hq : IsStarProjection q) :
    rectHSNorm r (U.val * q - q * U.val) ^ 2 =
      2 * matrixTraceReal r (q - (q * U.val * q)ᴴ * (q * U.val * q)) := by
  have hu : U.val * U.valᴴ = 1 := U.prop.2
  have hleft : matrixTraceReal r ((q * U.val)ᴴ * (q * U.val)) = matrixTraceReal r q := by
    rw [matrixProjection_compression_gram hq, matrixTraceReal_mul_comm r (U.valᴴ * q) U.val,
      ← Matrix.mul_assoc, hu, Matrix.one_mul]
  have hcross : matrixTraceReal r ((U.val * q)ᴴ * (q * U.val)) =
      matrixTraceReal r ((q * U.val * q)ᴴ * (q * U.val * q)) := by
    calc
      _ = matrixTraceReal r (((U.val * q)ᴴ * (q * U.val)) * q) := by
        rw [matrixTraceReal_mul_comm r ((U.val * q)ᴴ * (q * U.val)) q]
        simp only [Matrix.conjTranspose_mul, hq.isSelfAdjoint.isHermitian.eq,
          ← Matrix.mul_assoc, hq.isIdempotentElem.eq]
      _ = _ := by
        rw [show q * U.val * q = q * (U.val * q) from Matrix.mul_assoc _ _ _,
          matrixProjection_compression_gram hq]
        simp only [Matrix.mul_assoc]
  rw [rectHSNorm_sub_sq, matrixUnitary_projection_gram U hq, hleft, hcross, matrixTraceReal_sub]
  ring

omit [Fintype μ] in
theorem rectHSNorm_unitary_bad_corner_le (r : Nat) (U : Matrix.unitaryGroup ι ℂ)
    {q : Matrix ι ι ℂ} (hq : IsStarProjection q) :
    rectHSNorm r (q - q * U.val * q) ^ 2 ≤ 4 * matrixTraceReal r q := by
  have hqnorm : rectHSNorm r q ^ 2 = matrixTraceReal r q := by
    rw [← matrixTraceReal_gram, hq.isSelfAdjoint.isHermitian.eq, hq.isIdempotentElem.eq]
  have hBnorm : rectHSNorm r (q * U.val * q) ^ 2 ≤ matrixTraceReal r q := by
    rw [← matrixTraceReal_gram]
    exact matrixTraceReal_mono r (matrixUnitary_compression_gram_le U hq)
  have hh := rectHSNorm_add_sq_le r q (-(q * U.val * q))
  have hn : rectHSNorm r (-(q * U.val * q)) = rectHSNorm r (q * U.val * q) := by
    rw [← neg_one_smul ℂ (q * U.val * q), rectHSNorm_smul]
    norm_num
  rw [← sub_eq_add_neg, hn] at hh
  linarith only [hh, hqnorm, hBnorm]

theorem rectHSNorm_unitary_pinching_defect_sum (r : Nat) (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (hsum : ∑ i, E i = 1) (U : Matrix.unitaryGroup ι ℂ) :
    rectHSNorm r (U.val - matrixBlockPinch E U.val) ^ 2 =
      ∑ i, matrixTraceReal r (E i - (E i * U.val * E i)ᴴ * (E i * U.val * E i)) := by
  have hleft (i : μ) : E i * (E i * U.val * E i) = E i * U.val * E i := by
    simp only [← Matrix.mul_assoc, (hE i).isIdempotentElem.eq]
  have hgram : matrixTraceReal r ((matrixBlockPinch E U.val)ᴴ * matrixBlockPinch E U.val) =
      ∑ i, matrixTraceReal r ((E i * U.val * E i)ᴴ * (E i * U.val * E i)) := by
    rw [matrixBlockPinch, matrixCorner_sum_gram E _ hE horth hleft, matrixTraceReal_sum]
  have hu : U.valᴴ * U.val = 1 := U.prop.1
  rw [rectHSNorm_pinching_defect_gram r E hE horth, hu, hgram]
  simp only [matrixTraceReal_sub, Finset.sum_sub_distrib]
  rw [← matrixTraceReal_sum r Finset.univ E, hsum]

theorem rectHSNorm_unitary_pinching_commutator_sum (r : Nat) (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (hsum : ∑ i, E i = 1) (U : Matrix.unitaryGroup ι ℂ) :
    (∑ i, rectHSNorm r (U.val * E i - E i * U.val) ^ 2) =
      2 * rectHSNorm r (U.val - matrixBlockPinch E U.val) ^ 2 := by
  simp_rw [rectHSNorm_unitary_projection_commutator_sq r U (hE _)]
  rw [← Finset.mul_sum, rectHSNorm_unitary_pinching_defect_sum r E hE horth hsum U]

end ThomGame.Analysis
