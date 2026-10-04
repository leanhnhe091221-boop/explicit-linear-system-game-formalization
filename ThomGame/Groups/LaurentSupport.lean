module

public import ThomGame.Groups.LaurentAlgebra
public import ThomGame.Groups.CompressorGroup
public import Mathlib.Algebra.MonoidAlgebra.Support
public import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Polynomial support inside the Laurent ring

Support in any additive exponent cone defines a subring. The nonnegative
cone gives the polynomial subring needed for the strict-compression witness.
-/

@[expose] public noncomputable section
namespace ThomGame.LaurentModel

open Compressor
open scoped Pointwise

def nonnegativeCone : AddSubmonoid Exponent where
  carrier := {v | ∀ i, 0 ≤ v i}
  zero_mem' := by simp
  add_mem' hu hv i := add_nonneg (hu i) (hv i)

instance (v : Exponent) : Decidable (v ∈ nonnegativeCone) :=
  inferInstanceAs (Decidable (∀ i, 0 ≤ v i))

def supportedSubring (C : AddSubmonoid Exponent) : Subring Laurent where
  carrier := {p | ∀ v ∈ p.coeff.support, v ∈ C}
  zero_mem' := by simp
  one_mem' := by
    intro v hv
    have hone : (1 : ZMod 5) ≠ 0 := by decide +kernel
    have he : v = 0 := by
      simpa [AddMonoidAlgebra.one_def, Finsupp.single_apply, hone, eq_comm] using hv
    subst v
    exact C.zero_mem
  add_mem' := by
    intro p q hp hq v hv
    have h := Finsupp.support_add hv
    rcases Finset.mem_union.mp h with h | h
    · exact hp v h
    · exact hq v h
  neg_mem' := by
    intro p hp v hv
    apply hp v
    simpa only [AddMonoidAlgebra.coeff_neg, Finsupp.support_neg] using hv
  mul_mem' := by
    intro p q hp hq v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset p q hv)
    exact C.add_mem (hp a ha) (hq b hb)

theorem monomial_mem_supported_iff (C : AddSubmonoid Exponent) (v : Exponent) :
    monomial v ∈ supportedSubring C ↔ v ∈ C := by
  change (∀ u ∈ (monomial v).coeff.support, u ∈ C) ↔ v ∈ C
  have hone : (1 : ZMod 5) ≠ 0 := by decide +kernel
  simp [monomial, hone]

def polynomialSubring : Subring Laurent := supportedSubring nonnegativeCone

theorem positive_coefficient_mem (r : Root) (m : Coeff) (hm : positive (.inl (r, m)) = true) :
    coefficient m ∈ polynomialSubring := by
  apply (monomial_mem_supported_iff nonnegativeCone (coefficientExponent m)).mpr
  cases m with
  | none => exact nonnegativeCone.zero_mem
  | some p =>
    rcases p with ⟨c, σ⟩
    cases σ with
    | false => simp [positive] at hm
    | true =>
      have h : ∀ c : Axis, signedExponent c true ∈ nonnegativeCone := by decide +kernel
      exact h c

theorem backward_exponent_not_nonnegative :
    exponentAction ((integralShear root12)⁻¹) (signedExponent 1 true) ∉ nonnegativeCone := by
  decide +kernel

theorem backward_monomial_not_polynomial :
    monomial (exponentAction ((integralShear root12)⁻¹) (signedExponent 1 true)) ∉ polynomialSubring := by
  rw [polynomialSubring, monomial_mem_supported_iff]
  exact backward_exponent_not_nonnegative

end ThomGame.LaurentModel
