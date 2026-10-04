module

public import ThomGame.Quantum.ProjectiveMeasurement
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-! Finite positive operator-valued measurements and their positive square roots.

The positivity field uses the usual Loewner order on bounded operators, equivalently
self-adjointness and nonnegative quadratic forms. No dilation is part of the definition.
-/

@[expose] public section
namespace ThomGame.Quantum

open scoped BigOperators

variable (H O : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Fintype O]

/-- A finite positive operator-valued measurement on a complex Hilbert space. -/
structure POVM where
  effect : O → H →L[ℂ] H
  positive : ∀ a, 0 ≤ effect a
  complete : ∑ a, effect a = 1

namespace POVM

variable {H O} (P : POVM H O)

omit [CompleteSpace H] in
theorem isPositive (a : O) : (P.effect a).IsPositive :=
  ContinuousLinearMap.nonneg_iff_isPositive.mp (P.positive a)

theorem selfAdjoint (a : O) : IsSelfAdjoint (P.effect a) :=
  (P.isPositive a).isSelfAdjoint

omit [CompleteSpace H] in
theorem quadratic_nonneg (a : O) (ξ : H) :
    0 ≤ (inner ℂ ξ (P.effect a ξ)).re :=
  (P.isPositive a).re_inner_nonneg_right ξ

omit [CompleteSpace H] in
theorem sum_apply (ξ : H) : ∑ a, P.effect a ξ = ξ := by
  rw [← _root_.sum_apply, P.complete, one_apply_eq_self]

/-- The positive square root used in the finite-dimensional measurement dilation. -/
noncomputable def root (a : O) : H →L[ℂ] H := CFC.sqrt (P.effect a)

theorem root_nonneg (a : O) : 0 ≤ P.root a := CFC.sqrt_nonneg _

theorem root_selfAdjoint (a : O) : IsSelfAdjoint (P.root a) :=
  IsSelfAdjoint.of_nonneg (P.root_nonneg a)

theorem root_mul_root (a : O) : P.root a * P.root a = P.effect a :=
  CFC.sqrt_mul_sqrt_self _ (P.positive a)

theorem root_norm_sq (a : O) (ξ : H) :
    ‖P.root a ξ‖ ^ 2 = (inner ℂ ξ (P.effect a ξ)).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), ← ContinuousLinearMap.adjoint_inner_right,
    (P.root_selfAdjoint a).adjoint_eq, ← mul_apply_eq_comp, P.root_mul_root]
  rfl

theorem sum_root_norm_sq (ξ : H) : ∑ a, ‖P.root a ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by
  simp only [P.root_norm_sq]
  rw [← Complex.re_sum, ← inner_sum, P.sum_apply]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) ξ).symm

end POVM

namespace ProjectiveMeasurement

variable {H O} (P : ProjectiveMeasurement H O)

/-- A projective measurement is, in particular, a POVM. -/
def toPOVM : POVM H O where
  effect := P.proj
  positive a := by
    apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
    exact (ContinuousLinearMap.IsIdempotentElem.isPositive_iff_isSelfAdjoint
      (P.idempotent a)).mpr (P.selfAdjoint a)
  complete := P.complete

@[simp] theorem toPOVM_effect (a : O) : P.toPOVM.effect a = P.proj a := rfl

end ProjectiveMeasurement

end ThomGame.Quantum
