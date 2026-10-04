module

public import ThomGame.Analysis.MatrixIntertwinerSpectral
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Hilbert--Schmidt Lipschitz functional calculus

Expanding a rectangular intertwiner in the two spectral bases proves
the estimate without a commutativity assumption. Only scalar bounds
on the finite spectra are needed; the square-matrix difference bound
in ALT (2.5) is the special case with intertwiner equal to one.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators NNReal

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem rectHSNorm_cfc_intertwiner_sq_le (r : Nat)
    {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ}
    (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B)
    (f g : ℝ → ℝ) (C : ℝ)
    (hfg : ∀ i j, (f (hA.eigenvalues i) - g (hB.eigenvalues j)) ^ 2 ≤
      C * (hA.eigenvalues i - hB.eigenvalues j) ^ 2) (X : Matrix ι κ ℂ) :
    rectHSNorm r (cfc f A * X - X * cfc g B) ^ 2 ≤
      C * rectHSNorm r (A * X - X * B) ^ 2 := by
  rw [rectHSNorm_cfc_intertwiner_sq r hA hB,
    rectHSNorm_intertwiner_spectral_sq r hA hB, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg r)
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  calc
    _ ≤ ‖matrixIntertwinerBasis hA.eigenvectorUnitary hB.eigenvectorUnitary X i j‖ ^ 2 *
        (C * (hA.eigenvalues i - hB.eigenvalues j) ^ 2) :=
      mul_le_mul_of_nonneg_left (hfg i j) (sq_nonneg _)
    _ = _ := by ring

theorem rectHSNorm_cfc_intertwiner_le_of_spectral_bound (r : Nat)
    {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ}
    (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B)
    (f g : ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hfg : ∀ i j, |f (hA.eigenvalues i) - g (hB.eigenvalues j)| ≤
      L * |hA.eigenvalues i - hB.eigenvalues j|) (X : Matrix ι κ ℂ) :
    rectHSNorm r (cfc f A * X - X * cfc g B) ≤
      L * rectHSNorm r (A * X - X * B) := by
  have hs := rectHSNorm_cfc_intertwiner_sq_le r hA hB f g (L ^ 2) (fun i j => by
    have he := mul_self_le_mul_self (abs_nonneg _) (hfg i j)
    simpa only [← pow_two, mul_pow, sq_abs] using he) X
  have hn := rectHSNorm_nonneg r (cfc f A * X - X * cfc g B)
  have hm := mul_nonneg hL (rectHSNorm_nonneg r (A * X - X * B))
  nlinarith

theorem rectHSNorm_cfc_intertwiner_le (r : Nat)
    {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ}
    (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B)
    (f : ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ a b, |f a - f b| ≤ L * |a - b|) (X : Matrix ι κ ℂ) :
    rectHSNorm r (cfc f A * X - X * cfc f B) ≤
      L * rectHSNorm r (A * X - X * B) :=
  rectHSNorm_cfc_intertwiner_le_of_spectral_bound r hA hB f f hL
    (fun _ _ => hf _ _) X

theorem rectHSNorm_cfc_intertwiner_le_lipschitz (r : Nat)
    {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ}
    (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B)
    {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (X : Matrix ι κ ℂ) :
    rectHSNorm r (cfc f A * X - X * cfc f B) ≤
      (L : ℝ) * rectHSNorm r (A * X - X * B) := by
  apply rectHSNorm_cfc_intertwiner_le r hA hB f L.coe_nonneg _ X
  intro a b
  simpa only [Real.dist_eq] using hf.dist_le_mul a b

theorem rectHSNorm_cfc_sub_le (r : Nat) {A B : Matrix ι ι ℂ}
    (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B)
    (f : ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ a b, |f a - f b| ≤ L * |a - b|) :
    rectHSNorm r (cfc f A - cfc f B) ≤ L * rectHSNorm r (A - B) := by
  simpa only [Matrix.mul_one, Matrix.one_mul] using
    rectHSNorm_cfc_intertwiner_le r hA hB f hL hf (1 : Matrix ι ι ℂ)

theorem rectHSNorm_cfc_sub_le_lipschitz (r : Nat) {A B : Matrix ι ι ℂ}
    (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B)
    {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    rectHSNorm r (cfc f A - cfc f B) ≤ (L : ℝ) * rectHSNorm r (A - B) := by
  simpa only [Matrix.mul_one, Matrix.one_mul] using
    rectHSNorm_cfc_intertwiner_le_lipschitz r hA hB hf (1 : Matrix ι ι ℂ)

theorem hsNorm_cfc_sub_le {d : Nat} {A B : CMatrix d}
    (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B)
    (f : ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ a b, |f a - f b| ≤ L * |a - b|) :
    hsNorm (cfc f A - cfc f B) ≤ L * hsNorm (A - B) :=
  rectHSNorm_cfc_sub_le d hA hB f hL hf

theorem rectHSNorm_cfc_abs_intertwiner_le (r : Nat)
    {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ}
    (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B) (X : Matrix ι κ ℂ) :
    rectHSNorm r (cfc (abs : ℝ → ℝ) A * X - X * cfc (abs : ℝ → ℝ) B) ≤
      rectHSNorm r (A * X - X * B) := by
  simpa only [one_mul] using rectHSNorm_cfc_intertwiner_le r hA hB abs
    (L := 1) zero_le_one (fun a b => by simpa using abs_abs_sub_abs_le_abs_sub a b) X

theorem rectHSNorm_cfc_abs_sub_le (r : Nat) {A B : Matrix ι ι ℂ}
    (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B) :
    rectHSNorm r (cfc (abs : ℝ → ℝ) A - cfc (abs : ℝ → ℝ) B) ≤
      rectHSNorm r (A - B) := by
  simpa only [Matrix.mul_one, Matrix.one_mul] using
    rectHSNorm_cfc_abs_intertwiner_le r hA hB (1 : Matrix ι ι ℂ)

end ThomGame.Analysis
