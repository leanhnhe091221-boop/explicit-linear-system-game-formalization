module

public import ThomGame.Groups.LaurentExponents
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Data.ZMod.Basic

/-! The three-variable Laurent ring over F₅ and its integral change of exponents. -/

@[expose] public noncomputable section
namespace ThomGame.LaurentModel

open Compressor

abbrev Laurent := AddMonoidAlgebra (ZMod 5) Exponent

def monomial (v : Exponent) : Laurent := AddMonoidAlgebra.single v 1

theorem monomial_zero : monomial 0 = 1 := rfl

theorem monomial_add (u v : Exponent) : monomial (u + v) = monomial u * monomial v := by
  simp [monomial, AddMonoidAlgebra.single_mul_single]

def coefficient (m : Coeff) : Laurent := monomial (coefficientExponent m)

theorem coefficient_none : coefficient none = 1 := rfl

theorem five_eq_zero : (5 : Laurent) = 0 := by
  have h : (5 : ZMod 5) = 0 := by decide +kernel
  have hm := congrArg (algebraMap (ZMod 5) Laurent) h
  simpa only [map_ofNat, map_zero] using hm

theorem five_nsmul (p : Laurent) : (5 : Nat) • p = 0 := by
  rw [nsmul_eq_mul]
  change (5 : Laurent) * p = 0
  rw [five_eq_zero, zero_mul]

def ringAction (A : IntegralGroup) : Laurent ≃+* Laurent :=
  AddMonoidAlgebra.mapDomainRingEquiv (ZMod 5) (exponentAction A)

theorem ringAction_monomial (A : IntegralGroup) (v : Exponent) :
    ringAction A (monomial v) = monomial (exponentAction A v) := by
  simp [ringAction, monomial]

theorem ringAction_one (p : Laurent) : ringAction 1 p = p := by
  apply AddMonoidAlgebra.coeff_injective
  ext v
  simp [ringAction, exponentAction_one]

theorem ringAction_mul (A B : IntegralGroup) (p : Laurent) :
    ringAction (A * B) p = ringAction A (ringAction B p) := by
  simp only [ringAction, exponentAction_mul, AddMonoidAlgebra.mapDomainRingEquiv_trans,
    RingEquiv.trans_apply]

theorem shear_coefficient (s : Root) (ε σ : Bool) (c : Axis) :
    ringAction (if ε then integralShear s else (integralShear s)⁻¹) (coefficient (some (c, σ))) =
      if c = target s then coefficient (some (c, σ)) * coefficient (some (source s, signMul ε σ))
      else coefficient (some (c, σ)) := by
  simp only [coefficient, coefficientExponent, ringAction_monomial, shear_signedExponent]
  split <;> simp [monomial_add]

theorem recovery_coefficient (c : Axis) :
    ringAction (integralRecovery c) (coefficient (some (c, true))) = coefficient (some (c, false)) := by
  simp [coefficient, coefficientExponent, ringAction_monomial, recovery_signedExponent]

end ThomGame.LaurentModel
