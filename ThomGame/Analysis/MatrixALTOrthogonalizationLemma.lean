module

public import ThomGame.Analysis.MatrixBlockPolarCorrection

/-!
# ALT Lemma 3.4 for actual finite matrices

The independent-parameter exponential tilt and the block polar
correction produce a partial isometry with the same initial
projection, exactly block commuting final projection, and the
source energy bound 2 exp(4t) I(Y) + 32 t^(-1/2).
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq μ]

theorem exists_matrixPartialIsometry_ALT_lemma3_4 {h : Nat} [NeZero h]
    (U : Fin h → Matrix.unitaryGroup κ ℂ) (V : Fin h → Matrix.unitaryGroup ι ℂ)
    (E : μ → Matrix ι ι ℂ) (hE : ∀ i, IsStarProjection (E i))
    (horth : ∀ i j, i ≠ j → E i * E j = 0) (hsum : ∑ i, E i = 1)
    (hdim : Fintype.card ι ≤ 3 * Fintype.card κ)
    (hcomm : ∀ j i, (V j).val * E i = E i * (V j).val)
    {Y : Matrix ι κ ℂ} (hY : IsStarProjection (Yᴴ * Y)) {t : ℝ} (ht : 1 ≤ t) :
    ∃ Z : Matrix ι κ ℂ, IsStarProjection (Zᴴ * Z) ∧ Zᴴ * Z = Yᴴ * Y ∧
      (∀ i, Commute (Z * Zᴴ) (E i)) ∧
      matrixIntertwiningEnergy (Fintype.card κ) U V Z ≤
        2 * Real.exp (4 * t) * matrixIntertwiningEnergy (Fintype.card κ) U V Y +
          32 * t ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨s, _, hinit, hdefect, henergy⟩ :=
    exists_matrixPartitionPolarTilt_good_parameter U V E hE horth hsum hdim hcomm hY ht
  let YA := matrixExponentialPolarTilt t (matrixProjectionParameter E s) Y
  have hYA : IsStarProjection (YAᴴ * YA) := hinit.symm ▸ hY
  obtain ⟨Z, hZi, hZcomm, hZdist⟩ := exists_matrixPartialIsometry_block_correction
    (Fintype.card κ) E hE horth hsum hYA
  have hZinitial : Zᴴ * Z = Yᴴ * Y := hZi.trans hinit
  refine ⟨Z, hZinitial.symm ▸ hY, hZinitial, hZcomm, ?_⟩
  have hperturb := matrixIntertwiningEnergy_perturb_le (Fintype.card κ) U V Z YA
  have hdist : rectHSNorm (Fintype.card κ) (Z - YA) ^ 2 ≤ 16 * (Real.sqrt t)⁻¹ := by
    nlinarith
  have hpower : t ^ (-(1 / 2 : ℝ)) = (Real.sqrt t)⁻¹ := by
    rw [Real.rpow_neg (zero_le_one.trans ht), Real.sqrt_eq_rpow]
  rw [hpower]
  nlinarith

end ThomGame.Analysis
