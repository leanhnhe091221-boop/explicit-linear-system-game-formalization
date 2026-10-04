module

public import ThomGame.Analysis.FiniteUCPReconstruction
public import ThomGame.Analysis.FiniteUCPParameterBounds
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! Explicit dyadic parameters for the finite ALT construction. These are scalar
estimates; the smoothing hypotheses remain explicit in the application theorem. -/

@[expose] public section
namespace ThomGame.Analysis
noncomputable section

def finiteALTExplicitRho : ℝ := (1 / 2 : ℝ) ^ 300
def finiteALTExplicitPower : ℕ := 2 ^ 2500
def finiteALTExplicitEta : ℝ := (1 / 2 : ℝ) ^ 8000
def finiteALTExplicitEdit : ℝ := (1 / 2 : ℝ) ^ 3900
def finiteALTExplicitAlpha : ℝ := (1 / 2 : ℝ) ^ (2 ^ 32002 : ℕ)
def finiteALTExplicitBeta : ℝ := (1 / 2 : ℝ) ^ (2 ^ 40000 : ℕ)
def finiteALTExplicitTolerance : ℝ := (1 / 10 : ℝ) ^ 40

theorem finiteALT_half_pow_antitone {m n : ℕ} (h : m ≤ n) :
    (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ m :=
  pow_le_pow_of_le_one (by norm_num) (by norm_num) h

theorem finiteALT_half_pow_pos (n : ℕ) : 0 < (1 / 2 : ℝ) ^ n := by positivity

theorem finiteALT_geometric_bound {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (n : ℕ) :
    (n : ℝ) * r ^ n * (1 - r) ≤ 1 := by
  have h : (n : ℝ) * r ^ n * (1 - r) ≤ 1 - r ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hpow : r ^ (n + 1) ≤ r ^ n :=
        pow_le_pow_of_le_one hr hr1 (by omega)
      have hmul := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (show 0 ≤ (n : ℝ) + 1 by positivity))
        (sub_nonneg.mpr hr1)
      push_cast
      rw [pow_succ] at hmul ⊢
      nlinarith
  exact h.trans (sub_le_self _ (pow_nonneg hr n))

theorem finiteALT_geometric_le {g ε : ℝ} (hg : 0 < g) (hg1 : g ≤ 1)
    (n : ℕ) (hn : 1 ≤ (n : ℝ) * g * ε) :
    (1 - g) ^ n ≤ ε := by
  have h := finiteALT_geometric_bound (sub_nonneg.mpr hg1)
    (show 1 - g ≤ 1 by linarith) n
  have hng : 0 < (n : ℝ) * g := by
    have hnn : 0 ≤ (n : ℝ) * g := mul_nonneg (Nat.cast_nonneg _) hg.le
    by_contra hnot
    have hz : (n : ℝ) * g = 0 := le_antisymm (le_of_not_gt hnot) hnn
    rw [hz, zero_mul] at hn
    norm_num at hn
  have hh : (n : ℝ) * g * (1 - g) ^ n ≤ (n : ℝ) * g * ε := by nlinarith
  exact (mul_le_mul_iff_right₀ hng).mp hh

theorem finiteALT_exp_lower (m : ℕ) :
    (1 / 8 : ℝ) ^ m ≤ Real.exp (-(m : ℝ)) := by
  have he : (1 / 8 : ℝ) ≤ Real.exp (-1) := by
    rw [Real.exp_neg]
    simpa only [one_div] using
      (inv_le_inv₀ (by norm_num : (0 : ℝ) < 8) (Real.exp_pos 1)).mpr
        (Real.exp_one_lt_three.le.trans (by norm_num))
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 8) he m
  simpa only [← Real.exp_nat_mul, mul_neg_one] using hp

theorem finiteALT_explicit_alpha_pos : 0 < finiteALTExplicitAlpha :=
  finiteALT_half_pow_pos _

theorem finiteALT_explicit_beta_pos : 0 < finiteALTExplicitBeta :=
  finiteALT_half_pow_pos _

theorem finiteALT_explicit_beta_alpha :
    finiteALTExplicitBeta ≤ finiteALTExplicitAlpha ^ 2 / 64 := by
  have hm : 6 ≤ (2 : ℕ) ^ 32002 := by
    exact (by norm_num : 6 ≤ (2 : ℕ) ^ 3).trans
      (Nat.pow_le_pow_right (by decide) (by decide : 3 ≤ 32002))
  have hn : (2 : ℕ) ^ 32002 * 2 + 6 ≤ 2 ^ 40000 := by
    calc
      (2 : ℕ) ^ 32002 * 2 + 6 ≤ 2 ^ 32002 * 4 := by omega
      _ = 2 ^ 32004 := by rw [show 32004 = 32002 + 2 from rfl, pow_add]; norm_num
      _ ≤ 2 ^ 40000 := Nat.pow_le_pow_right (by decide) (by decide)
  have hh := finiteALT_half_pow_antitone hn
  unfold finiteALTExplicitBeta finiteALTExplicitAlpha
  rw [pow_add, pow_mul, show (1 / 2 : ℝ) ^ 6 = 1 / 64 by norm_num] at hh
  simpa only [div_eq_mul_inv, one_mul] using hh

theorem finiteALT_explicit_beta_small : finiteALTExplicitBeta ≤ (1 / 2 : ℝ) ^ 5000 := by
  apply finiteALT_half_pow_antitone
  exact (by norm_num : 5000 ≤ (2 : ℕ) ^ 13).trans
    (Nat.pow_le_pow_right (by decide) (by decide : 13 ≤ 40000))

theorem finiteALT_explicit_alpha_eta :
    finiteALTExplicitAlpha ≤ finiteALTExplicitEta ^ 4 := by
  have hn : 32000 ≤ (2 : ℕ) ^ 32002 :=
    (by norm_num : 32000 ≤ (2 : ℕ) ^ 15).trans
      (Nat.pow_le_pow_right (by decide) (by decide : 15 ≤ 32002))
  simpa only [finiteALTExplicitAlpha, finiteALTExplicitEta, ← pow_mul,
    show (8000 : ℕ) * 4 = 32000 from rfl] using finiteALT_half_pow_antitone hn

theorem finiteALT_explicit_alpha_exp :
    9 * finiteALTExplicitAlpha ≤ Real.exp (-(finiteALTExplicitEta ^ 4)⁻¹) := by
  let m : ℕ := 2 ^ 32000
  have hm : 4 ≤ m := by
    change (2 : ℕ) ^ 2 ≤ 2 ^ 32000
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by decide : 2 ≤ 32000)
  have hhalf : 9 * (1 / 2 : ℝ) ^ m ≤ 1 := by
    have h := finiteALT_half_pow_antitone hm
    norm_num only [show (1 / 2 : ℝ) ^ 4 = 1 / 16 by norm_num] at h
    linarith
  have ha : finiteALTExplicitAlpha = (1 / 2 : ℝ) ^ m * (1 / 8 : ℝ) ^ m := by
    unfold finiteALTExplicitAlpha
    have hexp : (2 : ℕ) ^ 32002 = m * 4 := by
      dsimp [m]
      rw [show 32002 = 32000 + 2 from rfl, pow_add]
      norm_num
    rw [hexp, mul_comm m 4, pow_mul, ← mul_pow]
    exact congrArg (fun x : ℝ => x ^ m) (by norm_num)
  have he : (finiteALTExplicitEta ^ 4)⁻¹ = (m : ℝ) := by
    dsimp [finiteALTExplicitEta, m]
    simp only [← pow_mul, show (8000 : ℕ) * 4 = 32000 from rfl,
      one_div, inv_pow, inv_inv, Nat.cast_pow, Nat.cast_ofNat]
  rw [ha, he, ← mul_assoc]
  exact (mul_le_of_le_one_left (pow_nonneg (by norm_num) _) hhalf).trans
    (finiteALT_exp_lower m)

theorem finiteALT_explicit_kappa_bounds {κ : ℝ} (hκ : (1 / 2 : ℝ) ^ 20 ≤ κ) :
    0 < κ ∧ κ⁻¹ ≤ (2 : ℝ) ^ 20 ∧ (Real.sqrt κ)⁻¹ ≤ (2 : ℝ) ^ 10 ∧
      (1 / 2 : ℝ) ^ 30 ≤ κ * Real.sqrt κ := by
  have hκ0 : 0 < κ := (finiteALT_half_pow_pos 20).trans_le hκ
  have hs : (1 / 2 : ℝ) ^ 10 ≤ Real.sqrt κ := by
    apply Real.le_sqrt_of_sq_le
    simpa only [← pow_mul] using hκ
  have hi := (inv_le_inv₀ hκ0 (finiteALT_half_pow_pos 20)).mpr hκ
  have hsi := (inv_le_inv₀ (Real.sqrt_pos.mpr hκ0) (finiteALT_half_pow_pos 10)).mpr hs
  have hp := mul_le_mul hκ hs (by positivity) hκ0.le
  refine ⟨hκ0, ?_, ?_, ?_⟩
  · simpa only [one_div, inv_pow, inv_inv] using hi
  · simpa only [one_div, inv_pow, inv_inv] using hsi
  · simpa only [← pow_add] using hp

theorem finiteALT_explicit_sqrt_rho :
    Real.sqrt finiteALTExplicitRho = (1 / 2 : ℝ) ^ 150 := by
  unfold finiteALTExplicitRho
  rw [show 300 = 150 * 2 from rfl, pow_mul, Real.sqrt_sq (by positivity)]

theorem finiteALT_explicit_sqrt_power :
    (Real.sqrt (finiteALTExplicitPower : ℝ))⁻¹ = (1 / 2 : ℝ) ^ 1250 := by
  unfold finiteALTExplicitPower
  rw [Nat.cast_pow, Nat.cast_ofNat, show 2500 = 1250 * 2 from rfl, pow_mul,
    Real.sqrt_sq (by positivity), ← inv_pow]
  simp only [one_div]

set_option exponentiation.threshold 10000 in
theorem finiteALT_explicit_eta_conditions {κ : ℝ}
    (hκ : (1 / 2 : ℝ) ^ 20 ≤ κ) :
    0 < finiteALTExplicitEta ∧ finiteALTExplicitEta ≤ 1 / 8 ∧
      finiteALTExplicitEta ≤ κ / 1024 ∧
      (1 + 61440 / (κ * Real.sqrt κ)) * finiteALTExplicitEta ≤ 1 := by
  obtain ⟨hκ0, _, _, hp⟩ := finiteALT_explicit_kappa_bounds hκ
  have hη : finiteALTExplicitEta ≤ (1 / 2 : ℝ) ^ 50 :=
    finiteALT_half_pow_antitone (by decide : 50 ≤ 8000)
  have hinv : (κ * Real.sqrt κ)⁻¹ ≤ (2 : ℝ) ^ 30 := by
    have hi := (inv_le_inv₀ (mul_pos hκ0 (Real.sqrt_pos.mpr hκ0))
      (finiteALT_half_pow_pos 30)).mpr hp
    simpa only [one_div, inv_pow, inv_inv] using hi
  refine ⟨finiteALT_half_pow_pos _, hη.trans (by norm_num), ?_, ?_⟩
  · exact hη.trans (by nlinarith [hκ])
  · have hη0 : 0 ≤ finiteALTExplicitEta := (finiteALT_half_pow_pos _).le
    have ht := mul_le_mul_of_nonneg_right
      (add_le_add_left (mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 61440)) 1) hη0
    have hfin : (61440 * (2 : ℝ) ^ 30 + 1) * finiteALTExplicitEta ≤ 1 := by
      nlinarith [hη]
    simpa only [div_eq_mul_inv, add_comm] using ht.trans hfin

set_option exponentiation.threshold 10000 in
theorem finiteALT_explicit_edit_bound {κ : ℝ}
    (hκ : (1 / 2 : ℝ) ^ 20 ≤ κ) (hκ1 : κ ≤ 1) :
    altPrunedEditBound κ finiteALTExplicitEta ≤ 2 * finiteALTExplicitEdit ^ 2 := by
  obtain ⟨hκ0, hi, _, _⟩ := finiteALT_explicit_kappa_bounds hκ
  have hη0 : 0 ≤ finiteALTExplicitEta := (finiteALT_half_pow_pos _).le
  have hη1 : finiteALTExplicitEta ≤ 1 := by
    exact (finiteALT_explicit_eta_conditions hκ).2.1.trans (by norm_num)
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr hκ0.le) hi 3)
      (by positivity : (0 : ℝ) ≤ 2 ^ 42)) hη0
  apply (finiteUCP_altPrunedEditBound_le hκ0 hκ1 hη0 hη1).trans
  apply hh.trans
  norm_num [finiteALTExplicitEta, finiteALTExplicitEdit]

set_option exponentiation.threshold 10000 in
theorem finiteALT_explicit_scalar_decay {κ : ℝ}
    (hκ : (1 / 2 : ℝ) ^ 20 ≤ κ) (hκ1 : κ ≤ 1) :
    (1 - κ ^ 2 / (2 : ℝ) ^ 28) ^ finiteALTExplicitPower ≤ finiteALTExplicitRho ^ 4 := by
  have hκ0 := (finiteALT_explicit_kappa_bounds hκ).1
  have hg0 : 0 < κ ^ 2 / (2 : ℝ) ^ 28 := by positivity
  have hg1 : κ ^ 2 / (2 : ℝ) ^ 28 ≤ 1 := by nlinarith [sq_nonneg (κ - 1)]
  apply finiteALT_geometric_le hg0 hg1
  have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ 20) hκ 2
  have hprod := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hsq (by positivity : (0 : ℝ) ≤ 2 ^ 28))
    (by positivity : (0 : ℝ) ≤ (finiteALTExplicitPower : ℝ))
  have hprod' := mul_le_mul_of_nonneg_right hprod
    (by positivity : (0 : ℝ) ≤ finiteALTExplicitRho ^ 4)
  apply le_trans _ hprod'
  norm_num [finiteALTExplicitPower, finiteALTExplicitRho]

set_option exponentiation.threshold 10000 in
theorem finiteALT_explicit_reconstruction_bounds {κ β : ℝ}
    (hκ : (1 / 2 : ℝ) ^ 20 ≤ κ) (hβ : β ≤ finiteALTExplicitBeta) :
    0 < finiteALTExplicitRho ∧ finiteALTExplicitRho ≤ 1 / 1024 ∧
    (3 * (finiteALTExplicitPower : ℝ) * finiteALTExplicitEdit +
      2 * (Real.sqrt κ)⁻¹ * (Real.sqrt (finiteALTExplicitPower : ℝ))⁻¹ +
      ((finiteALTExplicitPower : ℝ) + 2) * β ≤ finiteALTExplicitRho ^ 4) ∧
    (134 * Real.sqrt finiteALTExplicitRho +
      (finiteALTExplicitPower : ℝ) * finiteALTExplicitEdit +
      ((finiteALTExplicitPower : ℝ) + 2) * β ≤ finiteALTExplicitTolerance) ∧
    (2 * ((Real.sqrt (finiteALTExplicitPower : ℝ))⁻¹ +
      134 * Real.sqrt finiteALTExplicitRho +
      (finiteALTExplicitPower : ℝ) * finiteALTExplicitEdit) ≤ finiteALTExplicitTolerance) := by
  have hb := hβ.trans finiteALT_explicit_beta_small
  have hbt := mul_le_mul_of_nonneg_left hb
    (add_nonneg (Nat.cast_nonneg finiteALTExplicitPower) (by norm_num : (0 : ℝ) ≤ 2))
  have hki := (finiteALT_explicit_kappa_bounds hκ).2.2.1
  have hkt := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hki (by norm_num : (0 : ℝ) ≤ 2))
    (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ 1250)
  refine ⟨finiteALT_half_pow_pos _, ?_, ?_, ?_, ?_⟩
  · norm_num [finiteALTExplicitRho]
  · rw [finiteALT_explicit_sqrt_power]
    apply (add_le_add (add_le_add (le_refl _) hkt) hbt).trans
    norm_num [finiteALTExplicitPower, finiteALTExplicitEdit, finiteALTExplicitRho]
  · rw [finiteALT_explicit_sqrt_rho]
    apply (add_le_add (le_refl _) hbt).trans
    norm_num [finiteALTExplicitPower, finiteALTExplicitEdit, finiteALTExplicitTolerance]
  · rw [finiteALT_explicit_sqrt_power, finiteALT_explicit_sqrt_rho]
    norm_num [finiteALTExplicitPower, finiteALTExplicitEdit, finiteALTExplicitTolerance]

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra

/-- Concrete finite ALT: the double-exponential smoothing threshold suffices
for tolerance `10⁻⁴⁰`, simultaneously for the H and Q gap constants. -/
theorem exists_finiteUCP_ALT_algebra_explicit {d h : ℕ} [NeZero d] [NeZero h]
    (U : Fin h → UnitaryMatrix d) (Φ : CMatrix d →CP CMatrix d)
    (htrace : ∀ X, normalizedTrace (Φ X) = normalizedTrace X)
    {κ β : ℝ} (hκ : (1 / 2 : ℝ) ^ 20 ≤ κ) (hκ1 : κ ≤ 1)
    (hcontrol : FiniteUCPDefectControl U Φ.toLinearMap κ β)
    (hβ : β ≤ finiteALTExplicitBeta) :
    ∃ A : StarSubalgebra ℂ (CMatrix d),
      (∀ X, matrixOpNorm X ≤ 1 → hsNorm (X - matrixTraceProjection A X) ≤
        2 * (Real.sqrt κ)⁻¹ * Real.sqrt (matrixCoordinateEnergy U X) +
          finiteALTExplicitTolerance) ∧
      (∀ X ∈ A, matrixOpNorm X ≤ 1 → Real.sqrt (matrixCoordinateEnergy U X) ≤
        finiteALTExplicitTolerance) := by
  obtain ⟨hη, hη8, hηκ, hsmall⟩ := finiteALT_explicit_eta_conditions hκ
  obtain ⟨hρ, hρsmall, hidem, hdist, henergy⟩ :=
    finiteALT_explicit_reconstruction_bounds hκ hβ
  obtain ⟨A, _, hA⟩ := exists_finiteUCP_ALT_algebra U Φ htrace
    finiteALTExplicitPower (by exact pow_pos (by decide) _)
    (finiteALT_explicit_kappa_bounds hκ).1 hκ1 finiteALT_explicit_alpha_pos
    hη hη8 hηκ hsmall finiteALT_explicit_alpha_eta finiteALT_explicit_alpha_exp
    hcontrol (hβ.trans finiteALT_explicit_beta_alpha)
    (finiteALT_half_pow_pos 3900).le (finiteALT_explicit_edit_bound hκ hκ1)
    hρ hρsmall (finiteALT_explicit_scalar_decay hκ hκ1) hidem hdist henergy
  exact ⟨A, hA⟩

theorem finiteALT_explicit_H_kappa : (1 / 2 : ℝ) ^ 20 ≤ 1 / 14400 := by norm_num
theorem finiteALT_explicit_Q_kappa : (1 / 2 : ℝ) ^ 20 ≤ 1 / 360000 := by norm_num

end
end ThomGame.Analysis
