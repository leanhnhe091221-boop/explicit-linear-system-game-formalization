module

public import ThomGame.Analysis.MatrixALTIntertwiningDefect
public import ThomGame.Analysis.MatrixALTPartitionReduction

/-!
# Summing the actual ALT block errors

Orthogonal initial supports give a dimension-free bound on left
multiplication by the entire family. Applying the product rule to
both signs gives the explicit O(eta) bound in ALT (4.12).
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d h : Nat} {μ : Type*} [Fintype μ]

theorem rectHSNorm_family_mul_sum_le (r : Nat) (V : μ → CMatrix d)
    (hV : (∑ i, (V i)ᴴ * V i) ≤ 1) (X : CMatrix d) :
    (∑ i, rectHSNorm r (V i * X) ^ 2) ≤ rectHSNorm r X ^ 2 := by
  have hgram (i : μ) : (V i * X)ᴴ * (V i * X) = Xᴴ * ((V i)ᴴ * V i) * X := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  calc
    _ = matrixTraceReal r (Xᴴ * (∑ i, (V i)ᴴ * V i) * X) := by
      simp_rw [← matrixTraceReal_gram, hgram]
      rw [← matrixTraceReal_sum, ← Matrix.sum_mul, ← Matrix.mul_sum]
    _ ≤ matrixTraceReal r (Xᴴ * X) := by
      simpa only [Matrix.star_eq_conjTranspose, Matrix.mul_one] using
        matrixTraceReal_mono r (star_left_conjugate_le_conjugate hV X)
    _ = _ := matrixTraceReal_gram r X

theorem hsNorm_intertwining_family_sum_le (V : μ → CMatrix d)
    (hV : (∑ i, (V i)ᴴ * V i) ≤ 1) (u w : CMatrix d) :
    (∑ i, hsNorm (u * V i - V i * w) ^ 2) ≤
      2 * (∑ i, hsNorm (u * V i - V i * u) ^ 2) + 2 * hsNorm (u - w) ^ 2 := by
  have hi (i : μ) : hsNorm (u * V i - V i * w) ^ 2 ≤
      2 * hsNorm (u * V i - V i * u) ^ 2 + 2 * hsNorm (V i * (u - w)) ^ 2 := by
    have he : u * V i - V i * w = (u * V i - V i * u) + V i * (u - w) := by noncomm_ring
    rw [he]
    exact rectHSNorm_add_sq_le d _ _
  have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ => hi i
  have hm := rectHSNorm_family_mul_sum_le d V hV (u - w)
  simp only [rectHSNorm_eq_hsNorm, Finset.sum_add_distrib, ← Finset.mul_sum] at hm hs
  linarith only [hs, hm]

theorem matrixALTIntertwiningDefect_sum_le (U W : Fin h → UnitaryMatrix d) (V : μ → CMatrix d)
    (hV : (∑ i, (V i)ᴴ * V i) ≤ 1) :
    (∑ i, matrixALTIntertwiningDefect U W (V i)) ≤
      8 * (∑ i, matrixCoordinateEnergy U (V i)) +
        8 * lazyMarkovWeight h * ∑ j, hsNorm ((U j).val - (W j).val) ^ 2 := by
  have hj (j : Fin h) :
      (∑ i, (hsNorm ((U j).val * V i - V i * (W j).val) ^ 2 +
        hsNorm ((U j).valᴴ * V i - V i * (W j).valᴴ) ^ 2)) ≤
      4 * (∑ i, hsNorm ((U j).val * V i - V i * (U j).val) ^ 2) +
        4 * hsNorm ((U j).val - (W j).val) ^ 2 := by
    have hp := hsNorm_intertwining_family_sum_le V hV (U j).val (W j).val
    have hm := hsNorm_intertwining_family_sum_le V hV (U j).valᴴ (W j).valᴴ
    have hcomm (i : μ) : hsNorm ((U j).valᴴ * V i - V i * (U j).valᴴ) =
        hsNorm ((U j).val * V i - V i * (U j).val) := hsNorm_unitary_star_commutator (U j) (V i)
    simp only [hcomm, ← Matrix.conjTranspose_sub, hsNorm_conjTranspose] at hm
    rw [Finset.sum_add_distrib]
    linarith only [hp, hm]
  have he := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := Finset.univ) fun j _ => hj j)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (lazyMarkovWeight_nonneg h))
  have hleft : (∑ i, matrixALTIntertwiningDefect U W (V i)) =
      2 * lazyMarkovWeight h * ∑ j, ∑ i,
        (hsNorm ((U j).val * V i - V i * (W j).val) ^ 2 +
          hsNorm ((U j).valᴴ * V i - V i * (W j).valᴴ) ^ 2) := by
    simp only [matrixALTIntertwiningDefect, ← Finset.mul_sum]
    rw [Finset.sum_comm]
  have hswap : (∑ j, ∑ i, hsNorm ((U j).val * V i - V i * (U j).val) ^ 2) =
      ∑ i, ∑ j, hsNorm ((U j).val * V i - V i * (U j).val) ^ 2 := Finset.sum_comm
  rw [hleft]
  convert he using 1
  simp only [matrixCoordinateEnergy, Finset.sum_add_distrib, ← Finset.mul_sum, hswap]
  ring

theorem MatrixALTOrthogonalSelection.block_error_sum_le [NeZero h]
    (U W : Fin h → UnitaryMatrix d) {κ α η : ℝ} {R : CMatrix d}
    (sel : MatrixALTOrthogonalSelection U κ α η R)
    (hW : (∑ j, hsNorm ((W j).val - (U j).val) ^ 2) ≤ 37888 * (h : ℝ) * η ^ 2) :
    (∑ i : Fin sel.n, matrixALTBlockError U W (matrixClosedLowSpectralCut (sel.S i) (κ / 512)) (sel.V i)) ≤
      85248 * η ^ 2 + 6 * (512 / κ) ^ 2 * η := by
  have hV : (∑ i, (sel.V i)ᴴ * sel.V i) ≤ 1 :=
    (matrixProjection_sum _ sel.initial_projection sel.initial_orthogonal).le_one
  have he := matrixALTIntertwiningDefect_sum_le U W sel.V hV
  have hw := mul_le_mul_of_nonneg_left hW
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) (lazyMarkovWeight_nonneg h))
  simp_rw [hsNorm_sub_comm (U _).val (W _).val] at he
  have hc : 8 * lazyMarkovWeight h * (37888 * (h : ℝ) * η ^ 2) = 75776 * η ^ 2 := by
    calc
      _ = 303104 * (lazyMarkovWeight h * h) * η ^ 2 := by ring
      _ = _ := by rw [lazyMarkovWeight_mul_card]; ring
  rw [hc] at hw
  unfold matrixALTBlockError
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  linarith only [he, hw, sel.energy, sel.leakage]

end ThomGame.Analysis
