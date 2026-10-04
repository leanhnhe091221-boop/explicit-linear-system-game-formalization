module

public import ThomGame.Analysis.MatrixPolarMultiplier
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# Exponential polar tilting and ALT (3.9)

The actual exponential of a self-adjoint contraction has the required
coercivity and operator bound. Its polar action on a partial isometry
preserves the initial projection and multiplies intertwining energy
by at most exp(4t).
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] {h : Nat}

noncomputable def matrixRealExp (t : ℝ) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  cfc (fun s : ℝ => Real.exp (t * s)) A

theorem matrixRealExp_eq_exp (t : ℝ) {A : Matrix ι ι ℂ} (hA : Matrix.IsHermitian A) :
    matrixRealExp t A = NormedSpace.exp (t • A) := by
  rw [matrixRealExp, cfc_comp_const_mul t Real.exp A (by fun_prop) hA.isSelfAdjoint]
  apply CFC.real_exp_eq_normedSpace_exp
  show star (t • A) = t • A
  simp only [star_smul, star_trivial, hA.star_eq]

theorem matrixRealExp_isHermitian (t : ℝ) (A : Matrix ι ι ℂ) :
    Matrix.IsHermitian (matrixRealExp t A) := IsSelfAdjoint.cfc

theorem matrixRealExp_inverse (t : ℝ) {A : Matrix ι ι ℂ} (hA : Matrix.IsHermitian A) :
    matrixRealExp (-t) A * matrixRealExp t A = 1 := by
  rw [matrixRealExp, matrixRealExp, ← cfc_mul _ _ A
    (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
  calc
    _ = cfc (fun _ : ℝ => 1) A := by
      apply cfc_congr
      intro s _
      dsimp only
      rw [← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    _ = 1 := cfc_const_one ℝ A hA.isSelfAdjoint

theorem matrixRealExp_mul_self (t : ℝ) (A : Matrix ι ι ℂ) :
    matrixRealExp t A * matrixRealExp t A = matrixRealExp (2 * t) A := by
  rw [matrixRealExp, matrixRealExp, ← cfc_mul _ _ A
    (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
  apply cfc_congr
  intro s _
  dsimp only
  rw [← Real.exp_add]
  congr 1
  ring

theorem matrix_spectrum_abs_le_one {A : Matrix ι ι ℂ} (hA : Matrix.IsHermitian A)
    (hAnorm : ‖A‖ ≤ 1) {s : ℝ} (hs : s ∈ spectrum ℝ A) : |s| ≤ 1 := by
  have hid : cfc (fun t : ℝ => t) A = A := cfc_id ℝ A
  have he := norm_apply_le_norm_cfc (fun t : ℝ => t) A hs
  rw [hid, Real.norm_eq_abs] at he
  exact he.trans hAnorm

theorem matrixRealExp_norm_le {A : Matrix ι ι ℂ} (hA : Matrix.IsHermitian A)
    (hAnorm : ‖A‖ ≤ 1) {t : ℝ} (ht : 0 ≤ t) : ‖matrixRealExp t A‖ ≤ Real.exp t := by
  apply norm_cfc_le (Real.exp_nonneg t)
  intro s hs
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have he := (abs_le.mp (matrix_spectrum_abs_le_one hA hAnorm hs)).2
  nlinarith

theorem matrixRealExp_coercive {A : Matrix ι ι ℂ} (hA : Matrix.IsHermitian A)
    (hAnorm : ‖A‖ ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    (Real.exp (-t)) ^ 2 • (1 : Matrix ι ι ℂ) ≤ (matrixRealExp t A)ᴴ * matrixRealExp t A := by
  rw [(matrixRealExp_isHermitian t A).eq, matrixRealExp_mul_self]
  have hc : cfc (fun _ : ℝ => (Real.exp (-t)) ^ 2) A = (Real.exp (-t)) ^ 2 • (1 : Matrix ι ι ℂ) := by
    rw [cfc_const _ A hA.isSelfAdjoint, Algebra.algebraMap_eq_smul_one]
  rw [← hc, matrixRealExp]
  apply cfc_mono _ (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)
  intro s hs
  have he := (abs_le.mp (matrix_spectrum_abs_le_one hA hAnorm hs)).1
  rw [pow_two, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem matrixRealExp_commute {A W : Matrix ι ι ℂ} (hA : Matrix.IsHermitian A)
    (t : ℝ) (hW : W * A = A * W) : W * matrixRealExp t A = matrixRealExp t A * W := by
  exact (matrix_cfc_intertwine hA hA (fun s => Real.exp (t * s)) W hW.symm).symm

noncomputable def matrixExponentialPolarTilt (t : ℝ) (A : Matrix ι ι ℂ) (Y : Matrix ι κ ℂ) :
    Matrix ι κ ℂ := matrixRectPolar (matrixRealExp t A * Y)

theorem matrixExponentialPolarTilt_initial (t : ℝ) {A : Matrix ι ι ℂ}
    (hA : Matrix.IsHermitian A) {Y : Matrix ι κ ℂ} (hY : IsStarProjection (Yᴴ * Y)) :
    (matrixExponentialPolarTilt t A Y)ᴴ * matrixExponentialPolarTilt t A Y = Yᴴ * Y :=
  matrixRectPolar_initial_partial_isometry_left_inverse _ _ hY (matrixRealExp_inverse t hA)

theorem matrixExponentialPolarTilt_partial_isometry (t : ℝ) (A : Matrix ι ι ℂ) (Y : Matrix ι κ ℂ) :
    matrixExponentialPolarTilt t A Y * (matrixExponentialPolarTilt t A Y)ᴴ *
      matrixExponentialPolarTilt t A Y = matrixExponentialPolarTilt t A Y :=
  matrixRectPolar_partial_isometry _

theorem matrixExponentialPolarTilt_energy_le (r : Nat)
    (U : Fin h → Matrix.unitaryGroup κ ℂ) (V : Fin h → Matrix.unitaryGroup ι ℂ)
    {A : Matrix ι ι ℂ} (hA : Matrix.IsHermitian A) (hAnorm : ‖A‖ ≤ 1)
    {Y : Matrix ι κ ℂ} (hY : IsStarProjection (Yᴴ * Y)) {t : ℝ} (ht : 0 ≤ t)
    (hcomm : ∀ j, (V j).val * A = A * (V j).val) :
    matrixIntertwiningEnergy r U V (matrixExponentialPolarTilt t A Y) ≤
      Real.exp (4 * t) * matrixIntertwiningEnergy r U V Y := by
  have he := matrixIntertwiningEnergy_polar_mul_le r U V (matrixRealExp t A) (matrixRealExp (-t) A)
    hY (matrixRealExp_inverse t hA) (Real.exp_pos (-t)) (matrixRealExp_coercive hA hAnorm ht)
    (fun j => matrixRealExp_commute hA t (hcomm j))
  have hn := mul_self_le_mul_self (norm_nonneg _) (matrixRealExp_norm_le hA hAnorm ht)
  have hc : (Real.exp (-t))⁻¹ ^ 2 * (Real.exp t) ^ 2 = Real.exp (4 * t) := by
    rw [Real.exp_neg, inv_inv]
    simp only [pow_two, ← Real.exp_add]
    congr 1
    ring
  refine he.trans ?_
  rw [← hc]
  apply mul_le_mul_of_nonneg_right _ (matrixIntertwiningEnergy_nonneg r U V Y)
  exact mul_le_mul_of_nonneg_left (by simpa only [← pow_two] using hn) (sq_nonneg _)

end ThomGame.Analysis
