module

public import ThomGame.Groups.IntegralShearIntegerRoots
public import ThomGame.Groups.LaurentExponents

/-! The actual integral matrix image separates the integer parameters of each root. -/

@[expose] public section
namespace ThomGame.IntegralShear

open Compressor ElementaryMatrix LaurentModel

def integralMatrixModel : Model IntegralGroup where
  x := integralShear
  separated r s h := (integralShear_commute r s h).commutator_eq
  adjacent := integralShear_commutator
  torsion := integralShear_torsion

def toIntegralMatrix : ShearGroup →* IntegralGroup := integralMatrixModel.toHom

@[simp] theorem toIntegralMatrix_of (r : Root) : toIntegralMatrix (of r) = elem r 1 :=
  integralMatrixModel.toHom_of r

theorem integral_elem_zpow (r : Root) (m : ℤ) : (elem r (1 : ℤ)) ^ m = elem r m := by
  cases m with
  | ofNat n =>
      change (elem r (1 : ℤ)) ^ (n : ℤ) = elem r (n : ℤ)
      simp only [zpow_natCast, elem_pow, nsmul_eq_mul, mul_one]
  | negSucc n =>
      simp only [zpow_negSucc, elem_pow, elem_inv, nsmul_eq_mul, mul_one]
      rfl

@[simp] theorem toIntegralMatrix_rootElement (r : Root) (m : ℤ) :
    toIntegralMatrix (rootElement r m) = elem r m := by
  rw [rootElement, map_zpow, toIntegralMatrix_of, integral_elem_zpow]

theorem toIntegralMatrix_rootElement_entry (r : Root) (m : ℤ) :
    (toIntegralMatrix (rootElement r m) : Matrix Axis Axis ℤ) (source r) (target r) = m := by
  rw [toIntegralMatrix_rootElement, coe_elem]
  simp [source, target, r.property]

theorem rootElement_injective (r : Root) : Function.Injective (rootElement r) := by
  intro m n h
  have he := congrArg (fun g : ShearGroup =>
    (toIntegralMatrix g : Matrix Axis Axis ℤ) (source r) (target r)) h
  simpa only [toIntegralMatrix_rootElement_entry] using he

theorem rootElement_eq_one_iff (r : Root) (m : ℤ) : rootElement r m = 1 ↔ m = 0 := by
  rw [← rootElement_zero r, rootElement_injective r |>.eq_iff]

end ThomGame.IntegralShear
