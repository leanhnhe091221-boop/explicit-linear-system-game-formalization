module

public import ThomGame.Analysis.FiniteUCPHeatBounds
public import ThomGame.Analysis.MatrixMarkovCompletelyPositive
public import Mathlib.Algebra.Ring.GeomSum

/-! Finite smoothing from a weak spectral certificate tested on matrix
contractions. No operator spectral gap is inferred from this hypothesis. -/

@[expose] public section
namespace ThomGame.Analysis

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem finitePositivePower_energy_drop (T : H →L[ℂ] H)
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1) (x : H) :
    (inner ℂ (T x) ((1 - T) (T x))).re ≤
      (inner ℂ x ((1 - T) x)).re - ‖(1 - T) x‖ ^ 2 := by
  have hsT := (ContinuousLinearMap.nonneg_iff_isPositive.mp hT0).isSelfAdjoint
  have hA := ContinuousLinearMap.nonneg_iff_isPositive.mp (sub_nonneg.mpr hT1)
  have hid : (1 - T) - (1 - T) ^ 2 - T ^ 2 * (1 - T) =
      star (1 - T) * T * (1 - T) := by
    rw [star_sub, star_one, hsT.star_eq]
    noncomm_ring
  have hop : T ^ 2 * (1 - T) ≤ (1 - T) - (1 - T) ^ 2 := by
    apply sub_nonneg.mp
    rw [hid]
    exact star_left_conjugate_nonneg hT0 (1 - T)
  have hh := operator_re_inner_mono hop x
  have hp := finitePositivePower_energy_pairing T hT0 1 x
  simp only [mul_one, pow_one] at hp
  have hs := hA.inner_left_eq_inner_right x ((1 - T) x)
  have hn : (inner ℂ x (((1 - T : H →L[ℂ] H) ^ 2) x)).re = ‖(1 - T) x‖ ^ 2 := by
    rw [pow_two, mul_apply_eq_comp, ← hs]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  have hexpand : (inner ℂ x (((1 - T) - (1 - T) ^ 2 : H →L[ℂ] H) x)).re =
      (inner ℂ x ((1 - T) x)).re - ‖(1 - T) x‖ ^ 2 := by
    rw [sub_apply, inner_sub_right, Complex.sub_re, hn]
  rw [← hp, hexpand] at hh
  exact hh

end Hilbert

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra
variable {d h : ℕ} [NeZero d] [NeZero h]

/-- The bounded-test-matrix form of a robust quadratic spectral certificate. -/
def FiniteMatrixWeakGap (U : Fin h → UnitaryMatrix d) (lam ε : ℝ) : Prop :=
  ∀ X, matrixOpNorm X ≤ 1 → lam * matrixCoordinateEnergy U X ≤
    hsNorm (X - matrixLazyMarkov U X) ^ 2 + ε

theorem finiteUCP_matrix_energy_drop (U : Fin h → UnitaryMatrix d) (X : CMatrix d) :
    matrixCoordinateEnergy U (matrixLazyMarkov U X) ≤
      matrixCoordinateEnergy U X - hsNorm (X - matrixLazyMarkov U X) ^ 2 := by
  let : CompleteSpace (FiniteMatrixHilbert d) := FiniteDimensional.complete ℂ (FiniteMatrixHilbert d)
  let V := fun j => matrixConjugationHilbertEquiv (U j)
  have hh := finitePositivePower_energy_drop (lazyHilbertAverage V)
    (lazyHilbertAverage_nonneg V) (lazyHilbertAverage_le_one V) (finiteMatrixHilbertEquiv d X)
  have he (Y : CMatrix d) :
      (inner ℂ (finiteMatrixHilbertEquiv d Y)
        ((1 - lazyHilbertAverage V) (finiteMatrixHilbertEquiv d Y))).re =
          matrixCoordinateEnergy U Y := by
    rw [sub_apply, one_apply_eq_self, ← matrixLazyMarkov_hilbert, ← map_sub, finiteMatrixHilbert_inner]
    exact matrixLazyMarkov_energy U Y
  rw [← matrixLazyMarkov_hilbert, he, he, sub_apply, one_apply_eq_self,
    ← matrixLazyMarkov_hilbert, ← map_sub, finiteMatrixHilbert_norm] at hh
  exact hh

theorem finiteUCP_weakGap_energy_step (U : Fin h → UnitaryMatrix d)
    {lam ε : ℝ} (hgap : FiniteMatrixWeakGap U lam ε)
    (X : CMatrix d) (hX : matrixOpNorm X ≤ 1) :
    matrixCoordinateEnergy U (matrixLazyMarkov U X) ≤
      (1 - lam) * matrixCoordinateEnergy U X + ε := by
  have hg := hgap X hX
  have hd := finiteUCP_matrix_energy_drop U X
  linarith

theorem finiteUCP_weakGap_energy_power (U : Fin h → UnitaryMatrix d)
    {lam ε : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hε : 0 ≤ ε)
    (hgap : FiniteMatrixWeakGap U lam ε) (n : ℕ)
    (X : CMatrix d) (hX : matrixOpNorm X ≤ 1) :
    matrixCoordinateEnergy U ((matrixLazyMarkov U ^ n) X) ≤
      (1 - lam) ^ n * matrixCoordinateEnergy U X + ε / lam := by
  induction n with
  | zero =>
    simp only [pow_zero, Module.End.one_apply, one_mul]
    exact le_add_of_nonneg_right (div_nonneg hε hlam.le)
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    have hh := finiteUCP_weakGap_energy_step U hgap ((matrixLazyMarkov U ^ n) X)
      ((matrixLazyMarkov_pow_matrixOpNorm_le U n X).trans hX)
    apply hh.trans
    apply (add_le_add (mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hlam1)) (le_refl ε)).trans
    have he : (1 - lam) * ((1 - lam) ^ n * matrixCoordinateEnergy U X + ε / lam) + ε =
        (1 - lam) ^ (n + 1) * matrixCoordinateEnergy U X + ε / lam := by
      rw [pow_succ]
      field_simp [ne_of_gt hlam]
      ring
    exact he.le

theorem finiteUCP_sqrt_geometric_split {r a c : ℝ}
    (hr : 0 ≤ r) (ha : 0 ≤ a) (hc : 0 ≤ c) (n : ℕ) :
    Real.sqrt (r ^ n * a + c) ≤ (Real.sqrt r) ^ n * Real.sqrt a + Real.sqrt c := by
  have he : ((Real.sqrt r) ^ n) ^ 2 = r ^ n := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul, Real.sq_sqrt hr]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hs : ((Real.sqrt r) ^ n * Real.sqrt a) ^ 2 = r ^ n * a := by
    rw [mul_pow, he, Real.sq_sqrt ha]
  nlinarith [Real.sq_sqrt hc,
    mul_nonneg (mul_nonneg (pow_nonneg (Real.sqrt_nonneg r) n) (Real.sqrt_nonneg a))
      (Real.sqrt_nonneg c)]

theorem finiteUCP_weakGap_energy_sqrt_power (U : Fin h → UnitaryMatrix d)
    {lam ε : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hε : 0 ≤ ε)
    (hgap : FiniteMatrixWeakGap U lam ε) (n : ℕ)
    (X : CMatrix d) (hX : matrixOpNorm X ≤ 1) :
    Real.sqrt (matrixCoordinateEnergy U ((matrixLazyMarkov U ^ n) X)) ≤
      (Real.sqrt (1 - lam)) ^ n * Real.sqrt (matrixCoordinateEnergy U X) +
        Real.sqrt (ε / lam) :=
  (Real.sqrt_le_sqrt (finiteUCP_weakGap_energy_power U hlam hlam1 hε hgap n X hX)).trans
    (finiteUCP_sqrt_geometric_split (sub_nonneg.mpr hlam1)
      (matrixCoordinateEnergy_nonneg U X) (div_nonneg hε hlam.le) n)

theorem finiteUCP_sqrt_geometric_sum {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (n : ℕ) : ∑ k ∈ Finset.range n, (Real.sqrt (1 - lam)) ^ k ≤ 2 / lam := by
  let q := Real.sqrt (1 - lam)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq1 : q ≤ 1 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · nlinarith
  have hq2 : q ^ 2 = 1 - lam := Real.sq_sqrt (sub_nonneg.mpr hlam1)
  have hh := geom_sum_mul_neg q n
  have hsum : (∑ k ∈ Finset.range n, q ^ k) * (1 - q) ≤ 1 := by
    rw [hh]
    exact sub_le_self _ (pow_nonneg hq0 _)
  have hm := mul_le_mul_of_nonneg_right hsum (show 0 ≤ 1 + q by linarith)
  apply (le_div_iff₀ hlam).mpr
  change (∑ k ∈ Finset.range n, q ^ k) * lam ≤ 2
  have he : lam = (1 - q) * (1 + q) := by nlinarith
  rw [he, ← mul_assoc]
  exact hm.trans (by linarith)

theorem finiteUCP_weakGap_distance_sum (U : Fin h → UnitaryMatrix d)
    {lam ε : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hε : 0 ≤ ε)
    (hgap : FiniteMatrixWeakGap U lam ε) (n : ℕ)
    (X : CMatrix d) (hX : matrixOpNorm X ≤ 1) :
    hsNorm (X - (matrixLazyMarkov U ^ n) X) ≤
      (∑ k ∈ Finset.range n, (Real.sqrt (1 - lam)) ^ k) *
        Real.sqrt (matrixCoordinateEnergy U X) + (n : ℝ) * Real.sqrt (ε / lam) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : X - (matrixLazyMarkov U ^ (n + 1)) X =
        (X - (matrixLazyMarkov U ^ n) X) +
          ((matrixLazyMarkov U ^ n) X - matrixLazyMarkov U ((matrixLazyMarkov U ^ n) X)) := by
      rw [pow_succ', Module.End.mul_apply]
      abel
    have hstep : hsNorm ((matrixLazyMarkov U ^ n) X -
        matrixLazyMarkov U ((matrixLazyMarkov U ^ n) X)) ≤
        Real.sqrt (matrixCoordinateEnergy U ((matrixLazyMarkov U ^ n) X)) := by
      apply Real.le_sqrt_of_sq_le
      simpa only [matrixCoordinateEnergy, matrixLazyMarkov_energy] using
        matrixLazyMarkov_defect_norm_sq_le U ((matrixLazyMarkov U ^ n) X)
    have hs := hstep.trans (finiteUCP_weakGap_energy_sqrt_power U hlam hlam1 hε hgap n X hX)
    rw [he]
    apply (hsNorm_add_le _ _).trans
    apply (add_le_add ih hs).trans
    rw [Finset.sum_range_succ, Nat.cast_add_one]
    exact le_of_eq (by ring)

theorem finiteUCP_weakGap_distance (U : Fin h → UnitaryMatrix d)
    {lam ε : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hε : 0 ≤ ε)
    (hgap : FiniteMatrixWeakGap U lam ε) (n : ℕ)
    (X : CMatrix d) (hX : matrixOpNorm X ≤ 1) :
    hsNorm (X - (matrixLazyMarkov U ^ n) X) ≤
      (2 / lam) * Real.sqrt (matrixCoordinateEnergy U X) + (n : ℝ) * Real.sqrt (ε / lam) := by
  exact (finiteUCP_weakGap_distance_sum U hlam hlam1 hε hgap n X hX).trans
    (add_le_add (mul_le_mul_of_nonneg_right (finiteUCP_sqrt_geometric_sum hlam hlam1 n)
      (Real.sqrt_nonneg _)) (le_refl _))

theorem finiteUCP_weakGap_uniform_energy (U : Fin h → UnitaryMatrix d)
    {lam ε : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hε : 0 ≤ ε)
    (hgap : FiniteMatrixWeakGap U lam ε) (n : ℕ)
    (X : CMatrix d) (hX : matrixOpNorm X ≤ 1) :
    matrixCoordinateEnergy U ((matrixLazyMarkov U ^ n) X) ≤ (1 - lam) ^ n + ε / lam := by
  have hx := (hsNorm_le_matrixOpNorm X).trans hX
  have he : matrixCoordinateEnergy U X ≤ 1 :=
    (matrixCoordinateEnergy_le_hsNorm_sq U X).trans (by nlinarith [hsNorm_nonneg X])
  exact (finiteUCP_weakGap_energy_power U hlam hlam1 hε hgap n X hX).trans
    (add_le_add (mul_le_of_le_one_right (pow_nonneg (sub_nonneg.mpr hlam1) n) he) (le_refl _))

theorem finiteUCP_geometric_le_exp {lam : ℝ} (hlam1 : lam ≤ 1) (n : ℕ) :
    (1 - lam) ^ n ≤ Real.exp (-(n : ℝ) * lam) := by
  have hp := pow_le_pow_left₀ (sub_nonneg.mpr hlam1) (Real.one_sub_le_exp_neg lam) n
  simpa only [← Real.exp_nat_mul, mul_neg, neg_mul] using hp

theorem finiteUCP_weakGap_uniform_energy_exp (U : Fin h → UnitaryMatrix d)
    {lam ε : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hε : 0 ≤ ε)
    (hgap : FiniteMatrixWeakGap U lam ε) (n : ℕ)
    (X : CMatrix d) (hX : matrixOpNorm X ≤ 1) :
    matrixCoordinateEnergy U ((matrixLazyMarkov U ^ n) X) ≤
      Real.exp (-(n : ℝ) * lam) + ε / lam :=
  (finiteUCP_weakGap_uniform_energy U hlam hlam1 hε hgap n X hX).trans
    (add_le_add (finiteUCP_geometric_le_exp hlam1 n) (le_refl _))

/-- The concrete trace-preserving UCP heat map supplies both ALT inputs. -/
theorem finiteUCP_weakGap_defectControl (U : Fin h → UnitaryMatrix d)
    {lam ε β : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hε : 0 ≤ ε)
    (hgap : FiniteMatrixWeakGap U lam ε) (n : ℕ)
    (hβdist : (n : ℝ) * Real.sqrt (ε / lam) ≤ β)
    (hβenergy : Real.sqrt (Real.exp (-(n : ℝ) * lam) + ε / lam) ≤ β) :
    FiniteUCPDefectControl U (matrixMarkovPowerCP U n).toLinearMap (lam ^ 2 / 4) β := by
  have hroot : (Real.sqrt (lam ^ 2 / 4))⁻¹ = 2 / lam := by
    rw [show lam ^ 2 / 4 = (lam / 2) ^ 2 by ring, Real.sqrt_sq (by positivity), inv_div]
  refine ⟨(Real.sqrt_nonneg _).trans hβenergy, ?_, ?_⟩
  · intro X hX
    rw [hroot]
    exact (finiteUCP_weakGap_distance U hlam hlam1 hε hgap n X hX).trans
      (add_le_add (le_refl _) hβdist)
  · intro X hX
    exact (Real.sqrt_le_sqrt (finiteUCP_weakGap_uniform_energy_exp U hlam hlam1 hε hgap n X hX)).trans
      hβenergy

end ThomGame.Analysis
