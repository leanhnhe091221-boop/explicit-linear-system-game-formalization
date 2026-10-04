module

public import ThomGame.Analysis.MatrixPositiveResolvent
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Linear
public import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Differentiation of actual matrix resolvents

The affine resolvent is the actual matrix inverse. Its derivative is
proved using inversion in a normed algebra. Positive shifts provide
the required invertibility, including at the endpoints of a step.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {d : Nat}

theorem matrix_inverse_hasDerivAt {A : ℝ → CMatrix d} {B : CMatrix d} {t : ℝ}
    (hA : HasDerivAt A B t) (hunit : IsUnit (A t)) :
    HasDerivAt (fun s => (A s)⁻¹) (-(A t)⁻¹ * B * (A t)⁻¹) t := by
  obtain ⟨a, ha⟩ := hunit
  have hi := hasFDerivAt_ringInverse (𝕜 := ℝ) a
  rw [ha] at hi
  have hd := hi.comp_hasDerivAt t hA
  have hai : (↑a⁻¹ : CMatrix d) = Ring.inverse (A t) := by rw [← ha, Ring.inverse_unit]
  simpa only [Matrix.nonsing_inv_eq_ringInverse, neg_apply, Function.comp_def,
    ContinuousLinearMap.mulLeftRight_apply, neg_mul, hai] using! hd

noncomputable def matrixAffineResolvent (lam : ℝ) (S F : CMatrix d) (t : ℝ) : CMatrix d :=
  (lam • (1 : CMatrix d) + S + t • F)⁻¹

theorem matrixAffineResolvent_eq_positive {lam t : ℝ} {S F : CMatrix d}
    (hlam : 0 < lam) (hS : 0 ≤ S) (hF : 0 ≤ F) (ht : 0 ≤ t) :
    matrixAffineResolvent lam S F t = matrixPositiveResolvent lam (S + t • F) := by
  rw [matrixPositiveResolvent_eq_inverse hlam (add_nonneg hS (smul_nonneg ht hF)),
    matrixAffineResolvent, add_assoc]

theorem matrixAffineResolvent_hasDerivAt {lam t : ℝ} {S F : CMatrix d}
    (hlam : 0 < lam) (hS : 0 ≤ S) (hF : 0 ≤ F) (ht : 0 ≤ t) :
    HasDerivAt (matrixAffineResolvent lam S F)
      (-matrixAffineResolvent lam S F t * F * matrixAffineResolvent lam S F t) t := by
  have hpos : 0 ≤ S + t • F := add_nonneg hS (smul_nonneg ht hF)
  let a : (CMatrix d)ˣ :=
    ⟨lam • 1 + (S + t • F), matrixPositiveResolvent lam (S + t • F),
      matrixPositiveResolvent_shift_mul hlam hpos, matrixPositiveResolvent_mul_shift hlam hpos⟩
  have hu : IsUnit (lam • (1 : CMatrix d) + S + t • F) := by
    exact ⟨a, by dsimp [a]; rw [add_assoc]⟩
  have hd : HasDerivAt (fun s : ℝ => lam • (1 : CMatrix d) + S + s • F) F t := by
    simpa using ((hasDerivAt_id t).smul_const F).const_add (lam • (1 : CMatrix d) + S)
  exact matrix_inverse_hasDerivAt hd hu

theorem matrixAffineResolvent_continuousOn {lam : ℝ} {S F : CMatrix d}
    (hlam : 0 < lam) (hS : 0 ≤ S) (hF : 0 ≤ F) :
    ContinuousOn (matrixAffineResolvent lam S F) (Set.Ici 0) :=
  fun _ ht => (matrixAffineResolvent_hasDerivAt hlam hS hF ht).continuousAt.continuousWithinAt

end ThomGame.Analysis
