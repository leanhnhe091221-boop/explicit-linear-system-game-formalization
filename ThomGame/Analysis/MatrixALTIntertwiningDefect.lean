module

public import ThomGame.Analysis.MatrixALTCompressedExpansion
public import ThomGame.Analysis.MatrixProjectionCutNorm

/-!
# The two intertwining errors in ALT Theorem 4.3

The signed errors are actual matrices. Their normalization is precisely
1/(2h), and the commutator identity transfers half-rank expansion to
the reducing tuple with the error in ALT (4.12).
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d h : Nat}

theorem rectHSNorm_sub_sq_le (r : Nat) (X Y : CMatrix d) :
    rectHSNorm r (X - Y) ^ 2 ≤ 2 * rectHSNorm r X ^ 2 + 2 * rectHSNorm r Y ^ 2 := by
  have he := mul_self_le_mul_self (rectHSNorm_nonneg r (X - Y)) (rectHSNorm_sub_le r X Y)
  nlinarith [sq_nonneg (rectHSNorm r X - rectHSNorm r Y)]

theorem rectHSNorm_partialIsometry_mul_sq_le (r : Nat) {V : CMatrix d}
    (hV : IsStarProjection (Vᴴ * V)) (X : CMatrix d) :
    rectHSNorm r (V * X) ^ 2 ≤ rectHSNorm r X ^ 2 := by
  have hf : IsStarProjection (Vᴴᴴ * Vᴴ) := by
    simpa only [Matrix.conjTranspose_conjTranspose] using matrixPartialIsometry_final_projection hV
  have he := rectHSNorm_mul_sq_le_of_partialIsometry r Xᴴ hf
  simpa only [← Matrix.conjTranspose_mul, rectHSNorm_conjTranspose] using he

theorem matrixALT_transport_commutator (u w V q : CMatrix d) :
    u * (V * q * Vᴴ) - (V * q * Vᴴ) * u =
      V * (w * q - q * w) * Vᴴ + (u * V - V * w) * q * Vᴴ -
        V * q * (uᴴ * V - V * wᴴ)ᴴ := by
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  noncomm_ring

theorem rectHSNorm_ALT_transport_commutator_le (r : Nat) (u w : CMatrix d) {V q : CMatrix d}
    (hV : IsStarProjection (Vᴴ * V)) (hq : IsStarProjection q) :
    rectHSNorm r (u * (V * q * Vᴴ) - (V * q * Vᴴ) * u) ^ 2 ≤
      2 * rectHSNorm r (w * q - q * w) ^ 2 +
        4 * (rectHSNorm r (u * V - V * w) ^ 2 + rectHSNorm r (uᴴ * V - V * wᴴ) ^ 2) := by
  let A := V * (w * q - q * w) * Vᴴ
  let B := (u * V - V * w) * q * Vᴴ
  let C := V * q * (uᴴ * V - V * wᴴ)ᴴ
  have hf : IsStarProjection (Vᴴᴴ * Vᴴ) := by
    simpa only [Matrix.conjTranspose_conjTranspose] using matrixPartialIsometry_final_projection hV
  have hA : rectHSNorm r A ^ 2 ≤ rectHSNorm r (w * q - q * w) ^ 2 :=
    (rectHSNorm_mul_sq_le_of_partialIsometry r _ hf).trans (rectHSNorm_partialIsometry_mul_sq_le r hV _)
  have hB : rectHSNorm r B ^ 2 ≤ rectHSNorm r (u * V - V * w) ^ 2 :=
    (rectHSNorm_mul_sq_le_of_partialIsometry r _ hf).trans (rectHSNorm_mul_projection_sq_le r hq _)
  have hC : rectHSNorm r C ^ 2 ≤ rectHSNorm r (uᴴ * V - V * wᴴ) ^ 2 := by
    have he := (rectHSNorm_partialIsometry_mul_sq_le r hV (q * (uᴴ * V - V * wᴴ)ᴴ)).trans
      (rectHSNorm_projection_mul_sq_le r hq _)
    simpa only [← Matrix.mul_assoc, rectHSNorm_conjTranspose] using he
  have he := rectHSNorm_add_sq_le r A (B - C)
  have hbc := rectHSNorm_sub_sq_le r B C
  rw [matrixALT_transport_commutator]
  change rectHSNorm r (A + B - C) ^ 2 ≤ _
  rw [add_sub_assoc]
  linarith only [he, hbc, hA, hB, hC]

noncomputable def matrixALTIntertwiningDefect (U W : Fin h → UnitaryMatrix d) (V : CMatrix d) : ℝ :=
  2 * lazyMarkovWeight h * ∑ j,
    (hsNorm ((U j).val * V - V * (W j).val) ^ 2 +
      hsNorm ((U j).valᴴ * V - V * (W j).valᴴ) ^ 2)

theorem matrixALTIntertwiningDefect_nonneg (U W : Fin h → UnitaryMatrix d) (V : CMatrix d) :
    0 ≤ matrixALTIntertwiningDefect U W V := by
  unfold matrixALTIntertwiningDefect
  exact mul_nonneg (mul_nonneg (by norm_num) (lazyMarkovWeight_nonneg h))
    (Finset.sum_nonneg fun j _ => add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem matrixALTIntertwiningDefect_eq (U W : Fin h → UnitaryMatrix d) (V : CMatrix d) :
    matrixALTIntertwiningDefect U W V = (1 / (2 * (h : ℝ))) * ∑ j,
      (hsNorm ((U j).val * V - V * (W j).val) ^ 2 +
        hsNorm ((U j).valᴴ * V - V * (W j).valᴴ) ^ 2) := by
  unfold matrixALTIntertwiningDefect lazyMarkovWeight
  ring

theorem matrixCoordinateEnergy_ALT_transport_le (U W : Fin h → UnitaryMatrix d) {V q : CMatrix d}
    (hV : IsStarProjection (Vᴴ * V)) (hq : IsStarProjection q) :
    matrixCoordinateEnergy U (V * q * Vᴴ) ≤
      2 * matrixCoordinateEnergy W q + 2 * matrixALTIntertwiningDefect U W V := by
  have hj (j : Fin h) := rectHSNorm_ALT_transport_commutator_le d (U j).val (W j).val hV hq
  simp only [rectHSNorm_eq_hsNorm] at hj
  have he := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := Finset.univ) fun j _ => hj j)
    (lazyMarkovWeight_nonneg h)
  unfold matrixCoordinateEnergy matrixALTIntertwiningDefect
  convert he using 1
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

noncomputable def matrixALTBlockError (U W : Fin h → UnitaryMatrix d) (b V : CMatrix d) : ℝ :=
  matrixALTIntertwiningDefect U W V + 2 * matrixTraceReal d ((1 - b) * (V * Vᴴ))

theorem matrixALTBlockError_nonneg (U W : Fin h → UnitaryMatrix d) {b V : CMatrix d}
    (hb : IsStarProjection b) (hV : IsStarProjection (Vᴴ * V)) :
    0 ≤ matrixALTBlockError U W b V := by
  exact add_nonneg (matrixALTIntertwiningDefect_nonneg U W V)
    (mul_nonneg (by norm_num) (matrixTraceReal_projection_product_nonneg d hb.one_sub
      (matrixPartialIsometry_final_projection hV)))

theorem MatrixALTOrthogonalSelection.reducing_half_expansion [NeZero h]
    (U W : Fin h → UnitaryMatrix d) {κ α η : ℝ} {R : CMatrix d}
    (sel : MatrixALTOrthogonalSelection U κ α η R) (hR : IsStarProjection R)
    (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1) (i : Fin sel.n) {q : CMatrix d} (hq : IsStarProjection q)
    (hqP : q ≤ (sel.V i)ᴴ * sel.V i) (hqrank : 2 * q.rank ≤ ((sel.V i)ᴴ * sel.V i).rank) :
    κ / 1024 * matrixTraceReal d q -
        matrixALTBlockError U W (matrixClosedLowSpectralCut (sel.S i) (κ / 512)) (sel.V i) ≤
      matrixCoordinateEnergy W q := by
  have he := sel.transported_half_expansion U hR hκ hκ1 i hq hqP hqrank
  have ht := matrixCoordinateEnergy_ALT_transport_le U W (sel.initial_projection i) hq
  have hl := matrixTraceReal_projection_product_nonneg d
    (matrixClosedLowSpectralCut_isStarProjection (sel.S i) (κ / 512)).one_sub (sel.final_projection i)
  unfold matrixALTBlockError
  linarith only [he, ht, hl]

end ThomGame.Analysis
