module

public import ThomGame.Groups.ElementaryMatrix

/-!
# Integral exponent transformations

The six shears act on the exponent lattice Z³ by their actual integral
matrices. All finite identities below are checked by kernel evaluation.
-/

@[expose] public section
namespace ThomGame.LaurentModel

open Compressor ElementaryMatrix

abbrev Exponent := Axis → ℤ
abbrev IntegralGroup := Matrix.GeneralLinearGroup Axis ℤ

def exponentAction (A : IntegralGroup) : Exponent ≃+ Exponent where
  toFun v := Matrix.mulVec (A : Matrix Axis Axis ℤ) v
  invFun v := Matrix.mulVec (A⁻¹ : IntegralGroup) v
  left_inv v := by
    dsimp only
    rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
  right_inv v := by
    dsimp only
    rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
  map_add' := Matrix.mulVec_add _

theorem exponentAction_one : exponentAction 1 = AddEquiv.refl Exponent := by
  apply AddEquiv.ext
  intro v
  exact Matrix.one_mulVec v

theorem exponentAction_mul (A B : IntegralGroup) :
    exponentAction (A * B) = (exponentAction B).trans (exponentAction A) := by
  apply AddEquiv.ext
  intro v
  exact (Matrix.mulVec_mulVec v (A : Matrix Axis Axis ℤ) (B : Matrix Axis Axis ℤ)).symm

def signedExponent (c : Axis) (σ : Bool) : Exponent := Pi.single c (if σ then 1 else -1)

def coefficientExponent : Coeff → Exponent
  | none => 0
  | some (c, σ) => signedExponent c σ

def integralShear (s : Root) : IntegralGroup := elem s 1

def integralRecovery (c : Axis) : IntegralGroup :=
  (integralShear (cyclicRoot c) * (integralShear (reverse (cyclicRoot c)))⁻¹ *
    integralShear (cyclicRoot c)) ^ 2

theorem integralShear_commute (r s : Root) (hrs : separated r s) :
    Commute (integralShear r) (integralShear s) := elem_commute r s hrs 1 1

theorem integralShear_commutator (r : Root) :
    integralShear r * integralShear (right r) * (integralShear r)⁻¹ *
      (integralShear (right r))⁻¹ = integralShear (across r) := by
  simpa only [integralShear, one_mul] using elem_commutator r (1 : ℤ) 1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem integralShear_torsion :
    (integralShear root12 * (integralShear (reverse root12))⁻¹ * integralShear root12) ^ 4 = 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem shear_signedExponent : ∀ s ε c σ,
    exponentAction (if ε then integralShear s else (integralShear s)⁻¹) (signedExponent c σ) =
      if c = target s then signedExponent c σ + signedExponent (source s) (signMul ε σ)
      else signedExponent c σ := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem recovery_signedExponent : ∀ c σ,
    exponentAction (integralRecovery c) (signedExponent c σ) = signedExponent c (!σ) := by
  decide +kernel

end ThomGame.LaurentModel
