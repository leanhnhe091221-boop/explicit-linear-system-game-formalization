module

public import ThomGame.Analysis.FiniteUnitaryAverage
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.Linarith

/-! An exact regular representation which tests an approximate finite-group action.
The dilation is an actual linear isometry; its estimate is only required on the
chosen test vector, so it applies to normalized Hilbert--Schmidt errors. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open scoped BigOperators

variable {F H : Type*} [Group F] [Fintype F]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

abbrev FiniteRegularSpace (F H : Type*) [Fintype F] [NormedAddCommGroup H] :=
  PiLp 2 (fun _ : F => H)

def finiteRegularAction : F →* (FiniteRegularSpace F H ≃ₗᵢ[ℂ] FiniteRegularSpace F H) where
  toFun g := LinearIsometryEquiv.piLpCongrLeft 2 ℂ H (Equiv.mulLeft g)
  map_one' := by
    ext x k
    change x ((1 : F)⁻¹ * k) = x k
    simp
  map_mul' g h := by
    ext x k
    change x ((g*h)⁻¹ * k) = x (h⁻¹ * (g⁻¹ * k))
    simp only [mul_inv_rev, mul_assoc]

@[simp] theorem finiteRegularAction_apply (g : F) (x : FiniteRegularSpace F H) (k : F) :
    finiteRegularAction g x k = x (g⁻¹ * k) := rfl

def finiteDilationLinear (U : F → (H ≃ₗᵢ[ℂ] H)) : H →ₗ[ℂ] FiniteRegularSpace F H where
  toFun x := WithLp.toLp 2 (fun g => ((Real.sqrt (Fintype.card F))⁻¹ : ℂ) • U g⁻¹ x)
  map_add' x y := by ext g; simp [smul_add]
  map_smul' c x := by
    ext g
    change ((Real.sqrt (Fintype.card F))⁻¹ : ℂ) • U g⁻¹ (c • x) =
      c • (((Real.sqrt (Fintype.card F))⁻¹ : ℂ) • U g⁻¹ x)
    rw [map_smul, smul_comm]

@[simp] theorem finiteDilationLinear_apply (U : F → (H ≃ₗᵢ[ℂ] H)) (x : H) (g : F) :
    finiteDilationLinear U x g = ((Real.sqrt (Fintype.card F))⁻¹ : ℂ) • U g⁻¹ x := rfl

theorem finiteDilationLinear_norm (U : F → (H ≃ₗᵢ[ℂ] H)) (x : H) :
    ‖finiteDilationLinear U x‖ = ‖x‖ := by
  have hN : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hsq : (Real.sqrt (Fintype.card F)) ^ 2 = Fintype.card F := Real.sq_sqrt hN.le
  have hs : Real.sqrt (Fintype.card F) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hN)
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [finiteDilationLinear_apply, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _), LinearIsometryEquiv.norm_map,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_pow, inv_pow, hsq]
  field_simp [ne_of_gt hN]

def finiteDilation (U : F → (H ≃ₗᵢ[ℂ] H)) : H →ₗᵢ[ℂ] FiniteRegularSpace F H where
  toLinearMap := finiteDilationLinear U
  norm_map' := finiteDilationLinear_norm U

@[simp] theorem finiteDilation_apply (U : F → (H ≃ₗᵢ[ℂ] H)) (x : H) (g : F) :
    finiteDilation U x g = ((Real.sqrt (Fintype.card F))⁻¹ : ℂ) • U g⁻¹ x := rfl

theorem finiteDilation_intertwining_to (U : F → (H ≃ₗᵢ[ℂ] H)) (h : F) (V : H ≃ₗᵢ[ℂ] H) (x : H)
    {η : ℝ} (hη : 0 ≤ η)
    (hmul : ∀ g, ‖U g (V x) - U (g*h) x‖ ≤ η) :
    ‖finiteDilation U (V x) - finiteRegularAction h (finiteDilation U x)‖ ≤ η := by
  have hN : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hsq : (Real.sqrt (Fintype.card F)) ^ 2 = Fintype.card F := Real.sq_sqrt hN.le
  apply (sq_le_sq₀ (norm_nonneg _) hη).mp
  rw [PiLp.norm_sq_eq_of_L2]
  have hpoint (g : F) :
      ‖(finiteDilation U (V x) - finiteRegularAction h (finiteDilation U x)) g‖ ^ 2 ≤
      (Real.sqrt (Fintype.card F))⁻¹ ^ 2 * η ^ 2 := by
    change ‖((Real.sqrt (Fintype.card F))⁻¹ : ℂ) • U g⁻¹ (V x) -
      ((Real.sqrt (Fintype.card F))⁻¹ : ℂ) • U (h⁻¹ * g)⁻¹ x‖ ^ 2 ≤ _
    rw [← smul_sub, norm_smul, mul_pow]
    simp only [mul_inv_rev, inv_inv, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hmul g⁻¹) 2) (sq_nonneg _)
  refine (Finset.sum_le_sum (fun g _ => hpoint g)).trans_eq ?_
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, inv_pow, hsq]
  field_simp [ne_of_gt hN]

theorem finiteDilation_intertwining (U : F → (H ≃ₗᵢ[ℂ] H)) (h : F) (x : H)
    {η : ℝ} (hη : 0 ≤ η)
    (hmul : ∀ g, ‖U g (U h x) - U (g*h) x‖ ≤ η) :
    ‖finiteDilation U (U h x) - finiteRegularAction h (finiteDilation U x)‖ ≤ η :=
  finiteDilation_intertwining_to U h (U h) x hη hmul

end ThomGame.Analysis
