module

public import ThomGame.Analysis.FiniteUCPExplicitParameters
public import ThomGame.Analysis.FiniteUCPSandwich

/-! Pure scalar error budgets for the two finite heat lengths. Large natural
exponents are compared symbolically; no large real power is evaluated. -/

@[expose] public section
namespace ThomGame.Analysis

def finiteUCPExplicitRootHeatLength : ℕ := 2 ^ 40040
def finiteUCPExplicitShearHeatLength : ℕ := 2 ^ 40020

theorem finiteUCP_dyadic_scaled_le {a b c : ℕ} (h : a + b ≤ c) :
    (2 : ℝ) ^ a * (1 / 2 : ℝ) ^ c ≤ (1 / 2 : ℝ) ^ b := by
  calc
    _ ≤ (2 : ℝ) ^ a * (1 / 2 : ℝ) ^ (a + b) :=
      mul_le_mul_of_nonneg_left (finiteALT_half_pow_antitone h) (by positivity)
    _ = _ := by
      rw [pow_add, ← mul_assoc, ← mul_pow]
      norm_num

theorem finiteUCP_exp_le_dyadic {x : ℝ} {n : ℕ} (h : (n : ℝ) ≤ x) :
    Real.exp (-x) ≤ (1 / 2 : ℝ) ^ n := by
  have he : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
    rw [Real.exp_neg, one_div]
    exact (inv_le_inv₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 2)).mpr Real.exp_one_gt_two.le
  calc
    _ ≤ Real.exp (-(n : ℝ)) := Real.exp_le_exp.mpr (neg_le_neg h)
    _ = (Real.exp (-1)) ^ n := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le he n

theorem finiteUCP_sqrt_le_dyadic {x : ℝ} {n : ℕ}
    (h : x ≤ (1 / 2 : ℝ) ^ (n * 2)) : Real.sqrt x ≤ (1 / 2 : ℝ) ^ n := by
  apply Real.sqrt_le_iff.mpr
  exact ⟨(finiteALT_half_pow_pos _).le, by simpa only [pow_mul] using h⟩

theorem finiteUCP_noise_budget {C δ : ℝ} {c D a b ell : ℕ}
    (hδ0 : 0 ≤ δ) (hC : C ≤ (2 : ℝ) ^ c) (hδ : δ ≤ (1 / 2 : ℝ) ^ D)
    (hsmall : c + a * 2 ≤ D) (hscale : ell + b ≤ a) :
    ((2 ^ ell : ℕ) : ℝ) * Real.sqrt (C * δ) ≤ (1 / 2 : ℝ) ^ b := by
  have hc := mul_le_mul hC hδ hδ0 (by positivity : (0 : ℝ) ≤ 2 ^ c)
  have hr := finiteUCP_sqrt_le_dyadic (hc.trans (finiteUCP_dyadic_scaled_le hsmall))
  rw [Nat.cast_pow, Nat.cast_ofNat]
  exact (mul_le_mul_of_nonneg_left hr (by positivity)).trans (finiteUCP_dyadic_scaled_le hscale)

theorem finiteUCP_heat_energy_budget {C δ t : ℝ} {c D k b : ℕ}
    (hδ0 : 0 ≤ δ) (hC : C ≤ (2 : ℝ) ^ c) (hδ : δ ≤ (1 / 2 : ℝ) ^ D)
    (ht : (k : ℝ) ≤ t) (hsmall : c + k ≤ D) (hsqrt : 1 + b * 2 ≤ k) :
    Real.sqrt (Real.exp (-t) + C * δ) ≤ (1 / 2 : ℝ) ^ b := by
  have hc := (mul_le_mul hC hδ hδ0 (by positivity : (0 : ℝ) ≤ 2 ^ c)).trans
    (finiteUCP_dyadic_scaled_le hsmall)
  have he := finiteUCP_exp_le_dyadic ht
  apply finiteUCP_sqrt_le_dyadic
  have hh : Real.exp (-t) + C * δ ≤ (2 : ℝ) ^ 1 * (1 / 2 : ℝ) ^ k := by
    rw [pow_one]
    linarith
  exact hh.trans (finiteUCP_dyadic_scaled_le hsqrt)

theorem finiteUCP_small_add_doubleExponent {k : ℕ} (hk : k ≤ 49999) :
    230 + (2 : ℕ) ^ k ≤ 2 ^ 50000 := by
  have hc : 230 ≤ (2 : ℕ) ^ 49999 :=
    (by norm_num : 230 ≤ (2 : ℕ) ^ 8).trans
      (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by decide : 8 ≤ 49999))
  calc
    _ ≤ (2 : ℕ) ^ 49999 + 2 ^ 49999 :=
      add_le_add hc (Nat.pow_le_pow_right (by decide) hk)
    _ = _ := by rw [show 50000 = 49999 + 1 from rfl, pow_succ]; omega

theorem finiteUCP_doubleExponent_step {m k : ℕ} (hm : m ≤ (2 : ℕ) ^ k) :
    m + (2 : ℕ) ^ k ≤ 2 ^ (k + 1) := by rw [pow_succ]; omega

theorem finiteUCP_explicit_noise_budget {C δ : ℝ}
    (hδ0 : 0 ≤ δ) (hC : C ≤ (2 : ℝ) ^ 230) (hδ : δ ≤ (1 / 2 : ℝ) ^ (2 ^ 50000 : ℕ))
    {ell : ℕ} (hell : ell ≤ 40040) :
    ((2 ^ ell : ℕ) : ℝ) * Real.sqrt (C * δ) ≤ (1 / 2 : ℝ) ^ (2 ^ 49997 : ℕ) := by
  apply finiteUCP_noise_budget (a := 2 ^ 49998) hδ0 hC hδ
  · rw [← pow_succ (2 : ℕ) 49998]
    exact finiteUCP_small_add_doubleExponent (by decide : 49999 ≤ 49999)
  · apply finiteUCP_doubleExponent_step
    exact hell.trans ((by norm_num : 40040 ≤ (2 : ℕ) ^ 16).trans
      (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by decide : 16 ≤ 49997)))

theorem finiteUCP_explicit_root_heat_budget {C δ : ℝ}
    (hδ0 : 0 ≤ δ) (hC : C ≤ (2 : ℝ) ^ 230) (hδ : δ ≤ (1 / 2 : ℝ) ^ (2 ^ 50000 : ℕ)) :
    Real.sqrt (Real.exp (-(finiteUCPExplicitRootHeatLength : ℝ) / 60) + C * δ) ≤
      (1 / 2 : ℝ) ^ (2 ^ 40032 : ℕ) := by
  rw [neg_div]
  apply finiteUCP_heat_energy_budget (k := 2 ^ 40034) hδ0 hC hδ
  · change ((2 ^ 40034 : ℕ) : ℝ) ≤ (finiteUCPExplicitRootHeatLength : ℝ) / 60
    simp only [finiteUCPExplicitRootHeatLength, Nat.cast_pow, Nat.cast_ofNat]
    rw [show 40040 = 40034 + 6 from rfl, pow_add]
    norm_num only [show (2 : ℝ) ^ 6 = 64 by norm_num]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 60)).mpr
    exact mul_le_mul_of_nonneg_left (by norm_num : (60 : ℝ) ≤ 64) (by positivity)
  · exact finiteUCP_small_add_doubleExponent (by decide)
  · have hh : (1 : ℕ) ≤ 2 ^ 40033 := Nat.one_le_pow 40033 2 (by decide)
    rw [← pow_succ (2 : ℕ) 40032]
    exact finiteUCP_doubleExponent_step hh

theorem finiteUCP_explicit_shear_heat_budget {C δ : ℝ}
    (hδ0 : 0 ≤ δ) (hC : C ≤ (2 : ℝ) ^ 230) (hδ : δ ≤ (1 / 2 : ℝ) ^ (2 ^ 50000 : ℕ)) :
    Real.sqrt (Real.exp (-(finiteUCPExplicitShearHeatLength : ℝ) / 144) + C * δ) ≤
      (1 / 2 : ℝ) ^ (2 ^ 40010 : ℕ) := by
  rw [neg_div]
  apply finiteUCP_heat_energy_budget (k := 2 ^ 40012) hδ0 hC hδ
  · change ((2 ^ 40012 : ℕ) : ℝ) ≤ (finiteUCPExplicitShearHeatLength : ℝ) / 144
    simp only [finiteUCPExplicitShearHeatLength, Nat.cast_pow, Nat.cast_ofNat]
    rw [show 40020 = 40012 + 8 from rfl, pow_add]
    norm_num only [show (2 : ℝ) ^ 8 = 256 by norm_num]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 144)).mpr
    exact mul_le_mul_of_nonneg_left (by norm_num : (144 : ℝ) ≤ 256) (by positivity)
  · exact finiteUCP_small_add_doubleExponent (by decide)
  · have hh : (1 : ℕ) ≤ 2 ^ 40011 := Nat.one_le_pow 40011 2 (by decide)
    rw [← pow_succ (2 : ℕ) 40010]
    exact finiteUCP_doubleExponent_step hh

theorem finiteUCP_dyadic_double_antitone {m n : ℕ} (h : m ≤ n) :
    (1 / 2 : ℝ) ^ (2 ^ n : ℕ) ≤ (1 / 2 : ℝ) ^ (2 ^ m : ℕ) :=
  finiteALT_half_pow_antitone (Nat.pow_le_pow_right (by decide) h)

theorem finiteUCP_explicit_transport_exponent :
    24 + 2 * finiteUCPExplicitShearHeatLength + (2 : ℕ) ^ 40031 ≤ 2 ^ 40032 := by
  apply finiteUCP_doubleExponent_step
  have hsmall : 24 ≤ (2 : ℕ) ^ 40021 :=
    (by norm_num : 24 ≤ (2 : ℕ) ^ 5).trans
      (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by decide : 5 ≤ 40021))
  have hpower : 2 * finiteUCPExplicitShearHeatLength = (2 : ℕ) ^ 40021 := by
    unfold finiteUCPExplicitShearHeatLength
    rw [show 40021 = 40020 + 1 from rfl, pow_succ]
    omega
  rw [hpower]
  exact (finiteUCP_doubleExponent_step hsmall).trans
    (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by decide : 40022 ≤ 40031))

theorem finiteUCP_explicit_transport_budget {h : ℕ} {bN δ : ℝ}
    (hh : h ≤ 262144) (hbN0 : 0 ≤ bN)
    (hbN : bN ≤ (1 / 2 : ℝ) ^ (2 ^ 40032 : ℕ))
    (hδ : δ ≤ (1 / 2 : ℝ) ^ (2 ^ 50000 : ℕ)) :
    1680 * (4 : ℝ) ^ finiteUCPExplicitShearHeatLength *
      (8 * Real.sqrt (h : ℝ) * bN + 3 * δ) ≤ (1 / 2 : ℝ) ^ (2 ^ 40031 : ℕ) := by
  have hs : 8 * Real.sqrt (h : ℝ) ≤ 4096 := by
    have hr : Real.sqrt (h : ℝ) ≤ 512 := by
      apply Real.sqrt_le_iff.mpr
      exact ⟨by norm_num, by exact_mod_cast hh⟩
    linarith
  have hd := hδ.trans (finiteUCP_dyadic_double_antitone (by decide : 40032 ≤ 50000))
  have hi : 8 * Real.sqrt (h : ℝ) * bN + 3 * δ ≤
      (2 : ℝ) ^ 13 * (1 / 2 : ℝ) ^ (2 ^ 40032 : ℕ) := by
    have h1 := mul_le_mul hs hbN hbN0 (by norm_num : (0 : ℝ) ≤ 4096)
    have h2 := mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 3)
    have ht := finiteALT_half_pow_pos (2 ^ 40032)
    norm_num only [show (2 : ℝ) ^ 13 = 8192 by norm_num]
    linarith
  have hp : 0 ≤ (4 : ℝ) ^ finiteUCPExplicitShearHeatLength := by positivity
  have hleft : 1680 * (4 : ℝ) ^ finiteUCPExplicitShearHeatLength *
      (8 * Real.sqrt (h : ℝ) * bN + 3 * δ) ≤
      (2 : ℝ) ^ 11 * (4 : ℝ) ^ finiteUCPExplicitShearHeatLength *
        ((2 : ℝ) ^ 13 * (1 / 2 : ℝ) ^ (2 ^ 40032 : ℕ)) := by
    apply (mul_le_mul_of_nonneg_left hi (mul_nonneg (by norm_num) hp)).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by norm_num : (1680 : ℝ) ≤ 2 ^ 11) hp) (by positivity)
  have he : (2 : ℝ) ^ 11 * (4 : ℝ) ^ finiteUCPExplicitShearHeatLength *
      ((2 : ℝ) ^ 13 * (1 / 2 : ℝ) ^ (2 ^ 40032 : ℕ)) =
      (2 : ℝ) ^ (24 + 2 * finiteUCPExplicitShearHeatLength) *
        (1 / 2 : ℝ) ^ (2 ^ 40032 : ℕ) := by
    rw [pow_add, pow_mul]
    norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num,
      show (2 : ℝ) ^ 11 = 2048 by norm_num,
      show (2 : ℝ) ^ 13 = 8192 by norm_num,
      show (2 : ℝ) ^ 24 = 16777216 by norm_num]
    ring
  rw [he] at hleft
  exact hleft.trans (finiteUCP_dyadic_scaled_le finiteUCP_explicit_transport_exponent)

theorem finiteUCP_explicit_four_errors :
    4 * (1 / 2 : ℝ) ^ (2 ^ 40010 : ℕ) ≤ finiteALTExplicitBeta := by
  have hm : 2 ≤ (2 : ℕ) ^ 40000 := by
    simpa only [pow_one] using
      Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by decide : 1 ≤ 40000)
  have he : 2 + (2 : ℕ) ^ 40000 ≤ 2 ^ 40010 :=
    (finiteUCP_doubleExponent_step hm).trans
      (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by decide : 40001 ≤ 40010))
  simpa only [finiteALTExplicitBeta, show (2 : ℝ) ^ 2 = 4 by norm_num] using finiteUCP_dyadic_scaled_le he

theorem finiteUCP_explicit_sandwich_budget {h : ℕ} {νN νS bN bS δ : ℝ}
    (hh : h ≤ 262144) (hbN0 : 0 ≤ bN)
    (hνN : νN ≤ (1 / 2 : ℝ) ^ (2 ^ 49997 : ℕ))
    (hνS : νS ≤ (1 / 2 : ℝ) ^ (2 ^ 49997 : ℕ))
    (hbN : bN ≤ (1 / 2 : ℝ) ^ (2 ^ 40032 : ℕ))
    (hbS : bS ≤ (1 / 2 : ℝ) ^ (2 ^ 40010 : ℕ))
    (hδ : δ ≤ (1 / 2 : ℝ) ^ (2 ^ 50000 : ℕ)) :
    2 * νN + νS ≤ finiteALTExplicitBeta ∧
      bN + bS + 1680 * (4 : ℝ) ^ finiteUCPExplicitShearHeatLength *
        (8 * Real.sqrt (h : ℝ) * bN + 3 * δ) + νN ≤ finiteALTExplicitBeta := by
  have hνN' := hνN.trans (finiteUCP_dyadic_double_antitone (by decide : 40010 ≤ 49997))
  have hνS' := hνS.trans (finiteUCP_dyadic_double_antitone (by decide : 40010 ≤ 49997))
  have hbN' := hbN.trans (finiteUCP_dyadic_double_antitone (by decide : 40010 ≤ 40032))
  have ht := (finiteUCP_explicit_transport_budget hh hbN0 hbN hδ).trans
    (finiteUCP_dyadic_double_antitone (by decide : 40010 ≤ 40031))
  have hpos := finiteALT_half_pow_pos (2 ^ 40010)
  constructor
  · exact (by linarith : 2 * νN + νS ≤ 4 * (1 / 2 : ℝ) ^ (2 ^ 40010 : ℕ)).trans
      finiteUCP_explicit_four_errors
  · exact (by linarith : bN + bS + 1680 * (4 : ℝ) ^ finiteUCPExplicitShearHeatLength *
        (8 * Real.sqrt (h : ℝ) * bN + 3 * δ) + νN ≤ 4 * (1 / 2 : ℝ) ^ (2 ^ 40010 : ℕ)).trans
      finiteUCP_explicit_four_errors

end ThomGame.Analysis
