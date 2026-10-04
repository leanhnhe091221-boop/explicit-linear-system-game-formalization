module

public import ThomGame.Quantum.ProjectiveMeasurement
public import Mathlib.Algebra.Group.Commute.Basic

/-! Joint measurement of commuting projective families and relabelling outcomes. -/

@[expose] public section
namespace ThomGame.Quantum.ProjectiveMeasurement

open scoped BigOperators

variable {H A B C : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype A] [Fintype B] [Fintype C]

noncomputable def relabel (P : ProjectiveMeasurement H A) (e : B ≃ A) : ProjectiveMeasurement H B where
  proj b := P.proj (e b)
  selfAdjoint b := P.selfAdjoint (e b)
  idempotent b := P.idempotent (e b)
  orthogonal b c h := P.orthogonal _ _ (e.injective.ne h)
  complete := by rw [Equiv.sum_comp e P.proj, P.complete]

theorem cross_product (P : ProjectiveMeasurement H A) (Q : ProjectiveMeasurement H B)
    (hc : ∀ a b, Commute (P.proj a) (Q.proj b)) (a a' : A) (b b' : B) :
    (P.proj a * Q.proj b) * (P.proj a' * Q.proj b') =
      (P.proj a * P.proj a') * (Q.proj b * Q.proj b') := by
  calc
    (P.proj a * Q.proj b) * (P.proj a' * Q.proj b') =
        P.proj a * (Q.proj b * P.proj a') * Q.proj b' := by simp only [mul_assoc]
    _ = P.proj a * (P.proj a' * Q.proj b) * Q.proj b' := by rw [(hc a' b).eq]
    _ = (P.proj a * P.proj a') * (Q.proj b * Q.proj b') := by simp only [mul_assoc]

noncomputable def joint (P : ProjectiveMeasurement H A) (Q : ProjectiveMeasurement H B)
    (hc : ∀ a b, Commute (P.proj a) (Q.proj b)) : ProjectiveMeasurement H (A × B) where
  proj ab := P.proj ab.1 * Q.proj ab.2
  selfAdjoint ab := by
    change star (P.proj ab.1 * Q.proj ab.2) = _
    rw [star_mul, (Q.selfAdjoint ab.2).star_eq, (P.selfAdjoint ab.1).star_eq]
    exact (hc ab.1 ab.2).eq.symm
  idempotent ab := by rw [cross_product P Q hc, P.idempotent, Q.idempotent]
  orthogonal ab cd h := by
    rw [cross_product P Q hc]
    by_cases ha : ab.1 = cd.1
    · have hb : ab.2 ≠ cd.2 := fun hb => h (Prod.ext ha hb)
      rw [Q.orthogonal _ _ hb, mul_zero]
    · rw [P.orthogonal _ _ ha, zero_mul]
  complete := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, Q.complete, mul_one, P.complete]

theorem joint_proj (P : ProjectiveMeasurement H A) (Q : ProjectiveMeasurement H B)
    (hc : ∀ a b, Commute (P.proj a) (Q.proj b)) (a : A) (b : B) :
    (P.joint Q hc).proj (a, b) = P.proj a * Q.proj b := rfl

end ThomGame.Quantum.ProjectiveMeasurement
