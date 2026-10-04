module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Finite projective measurements on actual complex Hilbert spaces. -/

@[expose] public section
namespace ThomGame.Quantum

open scoped BigOperators

variable (H O : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Fintype O]

/-- A complete family of mutually orthogonal self-adjoint projections. -/
structure ProjectiveMeasurement where
  proj : O → H →L[ℂ] H
  selfAdjoint : ∀ a, IsSelfAdjoint (proj a)
  idempotent : ∀ a, proj a * proj a = proj a
  orthogonal : ∀ a b, a ≠ b → proj a * proj b = 0
  complete : ∑ a, proj a = 1

namespace ProjectiveMeasurement

variable {H O} (P : ProjectiveMeasurement H O)

theorem apply_twice (a : O) (ξ : H) : P.proj a (P.proj a ξ) = P.proj a ξ := by
  rw [← mul_apply_eq_comp, P.idempotent]

theorem sum_apply (ξ : H) : ∑ a, P.proj a ξ = ξ := by
  rw [← _root_.sum_apply, P.complete, one_apply_eq_self]

theorem norm_sq_apply (a : O) (ξ : H) :
    ‖P.proj a ξ‖ ^ 2 = (inner ℂ ξ (P.proj a ξ)).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), ← ContinuousLinearMap.adjoint_inner_right,
    (P.selfAdjoint a).adjoint_eq, P.apply_twice]
  rfl

theorem sum_norm_sq (ξ : H) : ∑ a, ‖P.proj a ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by
  simp only [P.norm_sq_apply]
  rw [← Complex.re_sum, ← inner_sum, P.sum_apply]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) ξ).symm

theorem apply_norm_sq_le (a : O) (ξ : H) : ‖P.proj a ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 := by
  rw [← P.sum_norm_sq ξ]
  exact Finset.single_le_sum (fun b _ => sq_nonneg ‖P.proj b ξ‖) (Finset.mem_univ a)

theorem inner_apply_eq_zero (a b : O) (hab : a ≠ b) (ξ ζ : H) :
    inner ℂ (P.proj a ξ) (P.proj b ζ) = 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_right, (P.selfAdjoint a).adjoint_eq,
    ← mul_apply_eq_comp, P.orthogonal a b hab, zero_apply, inner_zero_right]

/-- Always returning one prescribed outcome is a genuine projective measurement. -/
noncomputable def deterministic (a₀ : O) : ProjectiveMeasurement H O := by
  classical
  exact {
    proj := fun a => if a = a₀ then 1 else 0
    selfAdjoint := fun a => by split <;> simp
    idempotent := fun a => by split <;> simp
    orthogonal := fun a b hab => by
      by_cases ha : a = a₀
      · have hb : b ≠ a₀ := fun h => hab (ha.trans h.symm)
        simp [ha, hb]
      · simp [ha]
    complete := by simp }

theorem deterministic_apply [DecidableEq O] (a₀ a : O) (ξ : H) :
    (deterministic (H := H) a₀).proj a ξ = if a = a₀ then ξ else 0 := by
  classical
  by_cases h : a = a₀ <;> simp [deterministic, h]

end ProjectiveMeasurement

end ThomGame.Quantum
