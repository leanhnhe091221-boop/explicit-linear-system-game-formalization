module

public import ThomGame.Quantum.JointMeasurement
public import ThomGame.Quantum.BinaryMeasurement

/-! Finite functional calculus for a genuine projective measurement. -/

@[expose] public section
namespace ThomGame.Quantum.ProjectiveMeasurement

variable {H A B : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Fintype A] [Fintype B]

noncomputable def eval (P : ProjectiveMeasurement H A) (f : A → ℂ) : H →L[ℂ] H :=
  ∑ a, f a • P.proj a

variable (P : ProjectiveMeasurement H A)

theorem eval_one : P.eval (fun _ => 1) = 1 := by simp [eval, P.complete]

theorem eval_const (z : ℂ) : P.eval (fun _ => z) = z • 1 := by
  rw [eval, ← Finset.smul_sum, P.complete]

theorem eval_sub (f g : A → ℂ) : P.eval (fun a => f a - g a) = P.eval f - P.eval g := by
  simp only [eval, sub_smul, Finset.sum_sub_distrib]

theorem proj_eval (f : A → ℂ) (a : A) : P.proj a * P.eval f = f a • P.proj a := by
  classical
  rw [eval, Finset.mul_sum]
  rw [Finset.sum_eq_single a]
  · rw [mul_smul_comm, P.idempotent]
  · intro b _ hba
    rw [mul_smul_comm, P.orthogonal a b hba.symm, smul_zero]
  · simp

theorem eval_proj (f : A → ℂ) (a : A) : P.eval f * P.proj a = f a • P.proj a := by
  classical
  rw [eval, Finset.sum_mul]
  rw [Finset.sum_eq_single a]
  · rw [smul_mul_assoc, P.idempotent]
  · intro b _ hba
    rw [smul_mul_assoc, P.orthogonal b a hba, smul_zero]
  · simp

theorem eval_mul (f g : A → ℂ) : P.eval f * P.eval g = P.eval (fun a => f a * g a) := by
  rw [eval, Finset.sum_mul]
  simp only [smul_mul_assoc, P.proj_eval, smul_smul]
  rfl

theorem eval_commute (f g : A → ℂ) : Commute (P.eval f) (P.eval g) := by
  change _ = _
  rw [P.eval_mul, P.eval_mul]
  simp only [mul_comm]

theorem eval_selfAdjoint (f : A → ℂ) (hf : ∀ a, IsSelfAdjoint (f a)) :
    IsSelfAdjoint (P.eval f) := by
  change star (P.eval f) = P.eval f
  simp only [eval, star_sum, star_smul, (hf _).star_eq, (P.selfAdjoint _).star_eq]

theorem eval_norm_sq (f : A → ℂ) (ξ : H) :
    ‖P.eval f ξ‖ ^ 2 = ∑ a, ‖f a‖ ^ 2 * ‖P.proj a ξ‖ ^ 2 := by
  rw [← P.sum_norm_sq (P.eval f ξ)]
  apply Finset.sum_congr rfl
  intro a _
  rw [← mul_apply_eq_comp, P.proj_eval]
  simp only [smul_apply, norm_smul, mul_pow]

theorem joint_eval_left (Q : ProjectiveMeasurement H B)
    (hc : ∀ a b, Commute (P.proj a) (Q.proj b)) (f : A → ℂ) :
    (P.joint Q hc).eval (fun ab => f ab.1) = P.eval f := by
  simp only [eval, Fintype.sum_prod_type, joint_proj, ← Finset.smul_sum,
    ← Finset.mul_sum, Q.complete, mul_one]

theorem joint_eval_right (Q : ProjectiveMeasurement H B)
    (hc : ∀ a b, Commute (P.proj a) (Q.proj b)) (g : B → ℂ) :
    (P.joint Q hc).eval (fun ab => g ab.2) = Q.eval g := by
  simp only [eval, Fintype.sum_prod_type, joint_proj]
  rw [Finset.sum_comm]
  simp only [← Finset.smul_sum, ← Finset.sum_mul, P.complete, one_mul]

end ThomGame.Quantum.ProjectiveMeasurement
