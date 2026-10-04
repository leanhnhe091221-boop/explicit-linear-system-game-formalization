module

public import ThomGame.Groups.IntegralShearMatrixModel
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-! Actual copies of the integer plane and the two elementary conjugation actions. -/

@[expose] public section
namespace ThomGame.IntegralShear

open Compressor ElementaryMatrix

def rootPlaneElement (r : Root) (v : ℤ × ℤ) : ShearGroup :=
  rootElement (across r) v.1 * rootElement (right r) v.2

theorem rootPlane_factors_commute (r : Root) (m n : ℤ) :
    Commute (rootElement (across r) m) (rootElement (right r) n) :=
  rootElement_commute _ _ (by revert r; decide +kernel) m n

@[simp] theorem rootPlaneElement_zero (r : Root) : rootPlaneElement r 0 = 1 := by
  simp [rootPlaneElement]

theorem rootPlaneElement_add (r : Root) (v w : ℤ × ℤ) :
    rootPlaneElement r (v + w) = rootPlaneElement r v * rootPlaneElement r w := by
  simp only [rootPlaneElement, Prod.fst_add, Prod.snd_add, rootElement_add]
  exact (rootPlane_factors_commute r w.1 v.2).mul_mul_mul_comm _ _

def rootPlaneHom (r : Root) : Multiplicative (ℤ × ℤ) →* ShearGroup where
  toFun v := rootPlaneElement r v.toAdd
  map_one' := rootPlaneElement_zero r
  map_mul' v w := rootPlaneElement_add r v.toAdd w.toAdd

theorem toIntegralMatrix_rootPlaneElement (r : Root) (v : ℤ × ℤ) :
    (toIntegralMatrix (rootPlaneElement r v) : Matrix Axis Axis ℤ) =
      1 + Matrix.single (source r) (third r) v.1 + Matrix.single (target r) (third r) v.2 := by
  rw [rootPlaneElement, map_mul, Matrix.GeneralLinearGroup.coe_mul,
    toIntegralMatrix_rootElement, toIntegralMatrix_rootElement, coe_elem, coe_elem]
  change (1 + Matrix.single (source r) (third r) v.1) *
    (1 + Matrix.single (target r) (third r) v.2) = _
  simp [mul_add, add_mul, third_ne_target]

theorem rootPlaneElement_injective (r : Root) : Function.Injective (rootPlaneElement r) := by
  intro v w h
  have hm := congrArg (fun g : ShearGroup => (toIntegralMatrix g : Matrix Axis Axis ℤ)) h
  rw [toIntegralMatrix_rootPlaneElement, toIntegralMatrix_rootPlaneElement] at hm
  have h₁ := congrArg (fun M : Matrix Axis Axis ℤ => M (source r) (third r)) hm
  have h₂ := congrArg (fun M : Matrix Axis Axis ℤ => M (target r) (third r)) hm
  have hst : source r ≠ target r := r.property
  apply Prod.ext
  · simpa [Matrix.one_apply, Matrix.single, hst, hst.symm, (third_ne_source r).symm] using h₁
  · simpa [Matrix.one_apply, Matrix.single, hst, hst.symm, (third_ne_target r).symm] using h₂

theorem rootPlaneHom_injective (r : Root) : Function.Injective (rootPlaneHom r) :=
  rootPlaneElement_injective r

theorem rootPlaneElement_conjugate_upper (r : Root) (v : ℤ × ℤ) :
    of r * rootPlaneElement r v * (of r)⁻¹ = rootPlaneElement r (v.1 + v.2, v.2) := by
  have hfix := rootElement_commute r (across r) (by revert r; decide +kernel) 1 v.1
  rw [rootElement_one] at hfix
  have hmove := rootElement_conjugate r 1 v.2
  rw [rootElement_one, one_mul] at hmove
  change (MulAut.conj (of r)) (rootElement (across r) v.1 * rootElement (right r) v.2) = _
  rw [map_mul]
  change (of r * rootElement (across r) v.1 * (of r)⁻¹) *
    (of r * rootElement (right r) v.2 * (of r)⁻¹) = _
  rw [hfix.eq, mul_inv_cancel_right, hmove]
  simp only [rootPlaneElement, rootElement_add, mul_assoc]

theorem rootPlaneElement_conjugate_lower (r : Root) (v : ℤ × ℤ) :
    of (reverse r) * rootPlaneElement r v * (of (reverse r))⁻¹ =
      rootPlaneElement r (v.1, v.1 + v.2) := by
  have hr : right (reverse r) = across r := by revert r; decide +kernel
  have ha : across (reverse r) = right r := by clear hr; revert r; decide +kernel
  have hfix := rootElement_commute (reverse r) (right r)
    (by clear hr ha; revert r; decide +kernel) 1 v.2
  rw [rootElement_one] at hfix
  have hmove := rootElement_conjugate (reverse r) 1 v.1
  rw [rootElement_one, one_mul, hr, ha] at hmove
  change (MulAut.conj (of (reverse r))) (rootElement (across r) v.1 * rootElement (right r) v.2) = _
  rw [map_mul]
  change (of (reverse r) * rootElement (across r) v.1 * (of (reverse r))⁻¹) *
    (of (reverse r) * rootElement (right r) v.2 * (of (reverse r))⁻¹) = _
  rw [hfix.eq, mul_inv_cancel_right, hmove, (rootPlane_factors_commute r v.1 v.1).symm.eq]
  simp only [rootPlaneElement, rootElement_add, mul_assoc]

end ThomGame.IntegralShear
