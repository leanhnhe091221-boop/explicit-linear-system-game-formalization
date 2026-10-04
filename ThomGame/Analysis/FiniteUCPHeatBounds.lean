module

public import ThomGame.Analysis.FiniteUCPDefect
public import ThomGame.Analysis.MatrixUCPTraceBounds
public import ThomGame.Analysis.HilbertSpectralGap

/-! Finite, dimension-independent heat estimates without a spectral gap. -/

@[expose] public section
namespace ThomGame.Analysis

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem finitePositivePower_complement_antitone (T : H →L[ℂ] H)
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1) {m n : ℕ} (hmn : m ≤ n) :
    T ^ n * (1 - T) ≤ T ^ m * (1 - T) := by
  have hc (k : ℕ) : Commute (T ^ k) (1 - T) :=
    (Commute.one_right _).sub_right ((Commute.refl T).pow_left k)
  have hp := Commute.mul_nonneg
    (sub_nonneg.mpr (CStarAlgebra.pow_antitone hT1 hT0 hmn))
    (sub_nonneg.mpr hT1) ((hc m).sub_left (hc n))
  simpa only [sub_mul, sub_nonneg] using hp

theorem finitePositivePower_geometric_bound (T : H →L[ℂ] H)
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1) (n : ℕ) :
    n • (T ^ n * (1 - T)) ≤ 1 - T ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      (n + 1) • (T ^ (n + 1) * (1 - T)) ≤
          (n + 1) • (T ^ n * (1 - T)) :=
        nsmul_le_nsmul_right (finitePositivePower_complement_antitone T hT0 hT1 (by omega)) _
      _ = n • (T ^ n * (1 - T)) + T ^ n * (1 - T) := succ_nsmul _ _
      _ ≤ (1 - T ^ n) + T ^ n * (1 - T) :=
        add_le_add ih (le_refl (T ^ n * (1 - T)))
      _ = 1 - T ^ (n + 1) := by rw [mul_sub, mul_one, pow_succ]; abel

theorem finitePositivePower_energy_operator_bound (T : H →L[ℂ] H)
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1) (n : ℕ) :
    n • (T ^ (2 * n) * (1 - T)) ≤ 1 := by
  calc
    _ ≤ n • (T ^ n * (1 - T)) := nsmul_le_nsmul_right
      (finitePositivePower_complement_antitone T hT0 hT1 (by omega)) _
    _ ≤ 1 - T ^ n := finitePositivePower_geometric_bound T hT0 hT1 n
    _ ≤ 1 := sub_le_self _ (CStarAlgebra.pow_nonneg T n hT0)

theorem finitePositivePower_energy_pairing (T : H →L[ℂ] H) (hT0 : 0 ≤ T)
    (n : ℕ) (x : H) :
    inner ℂ ((T ^ n) x) ((1 - T) ((T ^ n) x)) =
      inner ℂ x ((T ^ (2 * n) * (1 - T)) x) := by
  have hs := (ContinuousLinearMap.nonneg_iff_isPositive.mp
    (CStarAlgebra.pow_nonneg T n hT0)).isSelfAdjoint.isSymmetric
  have he := hs x ((1 - T) ((T ^ n) x))
  change inner ℂ ((T ^ n) x) ((1 - T) ((T ^ n) x)) =
    inner ℂ x ((T ^ n) ((1 - T) ((T ^ n) x))) at he
  rw [he]
  congr 1
  have hc : Commute (1 - T) (T ^ n) :=
    ((Commute.one_right _).sub_right ((Commute.refl T).pow_left n)).symm
  change (T ^ n * ((1 - T) * T ^ n)) x = _
  rw [hc.eq, ← mul_assoc, ← pow_add, ← two_mul n]

theorem finitePositivePower_energy_bound (T : H →L[ℂ] H)
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1) (n : ℕ) (x : H) :
    (n : ℝ) * (inner ℂ ((T ^ n) x) ((1 - T) ((T ^ n) x))).re ≤ ‖x‖ ^ 2 := by
  have he := operator_re_inner_mono (finitePositivePower_energy_operator_bound T hT0 hT1 n) x
  rw [finitePositivePower_energy_pairing T hT0]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_apply, inner_smul_right] at he
  have hx : (inner ℂ x x).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
  simpa only [Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, zero_mul, sub_zero, one_apply_eq_self,
    hx] using he

end Hilbert

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra

variable {d h : ℕ} [NeZero d] [NeZero h]

theorem finiteUCP_matrixPower_energy_bound (U : Fin h → UnitaryMatrix d) (n : ℕ) (X : CMatrix d) :
    (n : ℝ) * matrixCoordinateEnergy U ((matrixLazyMarkov U ^ n) X) ≤ hsNorm X ^ 2 := by
  let : CompleteSpace (FiniteMatrixHilbert d) := FiniteDimensional.complete ℂ (FiniteMatrixHilbert d)
  let V := fun j => matrixConjugationHilbertEquiv (U j)
  have he := finitePositivePower_energy_bound (lazyHilbertAverage V)
    (lazyHilbertAverage_nonneg V) (lazyHilbertAverage_le_one V) n (finiteMatrixHilbertEquiv d X)
  have henergy (Y : CMatrix d) :
      (inner ℂ (finiteMatrixHilbertEquiv d Y)
        ((1 - lazyHilbertAverage V) (finiteMatrixHilbertEquiv d Y))).re =
          matrixCoordinateEnergy U Y := by
    rw [sub_apply, one_apply_eq_self, ← matrixLazyMarkov_hilbert, ← map_sub, finiteMatrixHilbert_inner]
    exact matrixLazyMarkov_energy U Y
  rw [← matrixLazyMarkov_pow_hilbert, henergy, finiteMatrixHilbert_norm] at he
  exact he

theorem finiteUCP_matrixPower_energy_sqrt_bound (U : Fin h → UnitaryMatrix d)
    (n : ℕ) (hn : 0 < n) (X : CMatrix d) (hX : matrixOpNorm X ≤ 1) :
    Real.sqrt (matrixCoordinateEnergy U ((matrixLazyMarkov U ^ n) X)) ≤
      (Real.sqrt (n : ℝ))⁻¹ := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hx : hsNorm X ≤ 1 := (hsNorm_le_matrixOpNorm X).trans hX
  have hx2 : hsNorm X ^ 2 ≤ 1 := by nlinarith [hsNorm_nonneg X]
  have he : matrixCoordinateEnergy U ((matrixLazyMarkov U ^ n) X) ≤ 1 / (n : ℝ) := by
    apply (le_div_iff₀ hnR).mpr
    simpa only [mul_comm] using (finiteUCP_matrixPower_energy_bound U n X).trans hx2
  have hs := Real.sqrt_le_sqrt he
  simpa only [one_div, Real.sqrt_inv] using hs

theorem finiteUCP_matrixPower_displacement (U : Fin h → UnitaryMatrix d)
    (n : ℕ) (X : CMatrix d) :
    hsNorm (X - (matrixLazyMarkov U ^ n) X) ≤
      (n : ℝ) * Real.sqrt (matrixCoordinateEnergy U X) := by
  have hstep : hsNorm (X - matrixLazyMarkov U X) ≤ Real.sqrt (matrixCoordinateEnergy U X) := by
    apply Real.le_sqrt_of_sq_le
    simpa only [matrixLazyMarkov_energy, matrixCoordinateEnergy] using
      matrixLazyMarkov_defect_norm_sq_le U X
  induction n with
  | zero => simp
  | succ n ih =>
    have he : X - (matrixLazyMarkov U ^ (n + 1)) X =
        (X - (matrixLazyMarkov U ^ n) X) + (matrixLazyMarkov U ^ n) (X - matrixLazyMarkov U X) := by
      rw [pow_succ, Module.End.mul_apply, map_sub]
      abel
    rw [he]
    calc
      _ ≤ hsNorm (X - (matrixLazyMarkov U ^ n) X) +
          hsNorm ((matrixLazyMarkov U ^ n) (X - matrixLazyMarkov U X)) := hsNorm_add_le _ _
      _ ≤ (n : ℝ) * Real.sqrt (matrixCoordinateEnergy U X) +
          Real.sqrt (matrixCoordinateEnergy U X) :=
        add_le_add ih ((matrixLazyMarkov_pow_hsNorm_le U n _).trans hstep)
      _ = _ := by rw [Nat.cast_add, Nat.cast_one]; ring

theorem finiteUCP_matrixPower_distance (U : Fin h → UnitaryMatrix d)
    (Φ : CMatrix d →ₗ[ℂ] CMatrix d) {κ β : ℝ}
    (hcontrol : FiniteUCPDefectControl U Φ κ β)
    (n : ℕ) (X : CMatrix d) (hX : matrixOpNorm X ≤ 1) :
    hsNorm (X - (matrixLazyMarkov U ^ n) X) ≤
      2 * (Real.sqrt κ)⁻¹ * Real.sqrt (matrixCoordinateEnergy U X) + ((n : ℝ) + 2) * β := by
  have he : X - (matrixLazyMarkov U ^ n) X = (X - Φ X) +
      (Φ X - (matrixLazyMarkov U ^ n) (Φ X)) + (matrixLazyMarkov U ^ n) (Φ X - X) := by
    rw [map_sub]
    abel
  have hdist := hcontrol.distance X hX
  have hmid := (finiteUCP_matrixPower_displacement U n (Φ X)).trans
    (mul_le_mul_of_nonneg_left (hcontrol.energy X hX) (Nat.cast_nonneg n))
  have hlast := matrixLazyMarkov_pow_hsNorm_le U n (Φ X - X)
  rw [hsNorm_sub_comm (Φ X) X] at hlast
  rw [he]
  have ht := (hsNorm_add_le ((X - Φ X) + (Φ X - (matrixLazyMarkov U ^ n) (Φ X)))
    ((matrixLazyMarkov U ^ n) (Φ X - X))).trans
      (add_le_add (hsNorm_add_le (X - Φ X) (Φ X - (matrixLazyMarkov U ^ n) (Φ X)))
        (le_refl (hsNorm ((matrixLazyMarkov U ^ n) (Φ X - X)))))
  linarith

theorem finiteUCP_matrixPower_idempotence (U : Fin h → UnitaryMatrix d)
    (Φ : CMatrix d →ₗ[ℂ] CMatrix d) {κ β : ℝ}
    (hcontrol : FiniteUCPDefectControl U Φ κ β) (n : ℕ) (hn : 0 < n) :
    matrixMixedNorm ((matrixLazyMarkov U ^ n).comp (matrixLazyMarkov U ^ n) -
      matrixLazyMarkov U ^ n) ≤
        2 * (Real.sqrt κ)⁻¹ * (Real.sqrt (n : ℝ))⁻¹ + ((n : ℝ) + 2) * β := by
  have hβ := hcontrol.beta_nonneg
  apply matrixMixedNorm_le_of_unit_bound _ _ (by positivity)
  intro X hX
  change hsNorm ((matrixLazyMarkov U ^ n) ((matrixLazyMarkov U ^ n) X) -
    (matrixLazyMarkov U ^ n) X) ≤ _
  rw [hsNorm_sub_comm]
  have hy := (matrixLazyMarkov_pow_matrixOpNorm_le U n X).trans hX
  exact (finiteUCP_matrixPower_distance U Φ hcontrol n _ hy).trans
    (add_le_add (mul_le_mul_of_nonneg_left
      (finiteUCP_matrixPower_energy_sqrt_bound U n hn X hX)
      (show 0 ≤ 2 * (Real.sqrt κ)⁻¹ by positivity)) (le_refl (((n : ℝ) + 2) * β)))

theorem finiteUCP_energy_sqrt_transfer (U : Fin h → UnitaryMatrix d) (X Y : CMatrix d) :
    Real.sqrt (matrixCoordinateEnergy U X) ≤
      2 * Real.sqrt (matrixCoordinateEnergy U Y) + 2 * hsNorm (X - Y) := by
  have hb (j : Fin h) : hsNorm ((U j).val * X - X * (U j).val) ^ 2 ≤
      2 * hsNorm ((U j).val * Y - Y * (U j).val) ^ 2 +
        2 * hsNorm ((U j).val * (X - Y) - (X - Y) * (U j).val) ^ 2 := by
    have he : (U j).val * X - X * (U j).val =
        ((U j).val * Y - Y * (U j).val) +
          ((U j).val * (X - Y) - (X - Y) * (U j).val) := by
      simp only [mul_sub, sub_mul]
      abel
    rw [he]
    have hs := hsNorm_add_le ((U j).val * Y - Y * (U j).val)
      ((U j).val * (X - Y) - (X - Y) * (U j).val)
    nlinarith [hsNorm_nonneg (((U j).val * Y - Y * (U j).val) +
      ((U j).val * (X - Y) - (X - Y) * (U j).val)),
      hsNorm_nonneg ((U j).val * Y - Y * (U j).val),
      hsNorm_nonneg ((U j).val * (X - Y) - (X - Y) * (U j).val),
      sq_nonneg (hsNorm ((U j).val * Y - Y * (U j).val) -
        hsNorm ((U j).val * (X - Y) - (X - Y) * (U j).val))]
  have he := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := Finset.univ) (fun j _ => hb j))
    (lazyMarkovWeight_nonneg h)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, mul_add] at he
  have he' : matrixCoordinateEnergy U X ≤
      2 * matrixCoordinateEnergy U Y + 2 * matrixCoordinateEnergy U (X - Y) := by
    dsimp only [matrixCoordinateEnergy]
    convert he using 1
    ring
  have hnorm := matrixCoordinateEnergy_le_hsNorm_sq U (X - Y)
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact add_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (mul_nonneg (by norm_num) (hsNorm_nonneg _))
  · have hs := Real.sq_sqrt (matrixCoordinateEnergy_nonneg U Y)
    nlinarith [Real.sqrt_nonneg (matrixCoordinateEnergy U Y), hsNorm_nonneg (X - Y),
      mul_nonneg (Real.sqrt_nonneg (matrixCoordinateEnergy U Y)) (hsNorm_nonneg (X - Y))]

end ThomGame.Analysis
