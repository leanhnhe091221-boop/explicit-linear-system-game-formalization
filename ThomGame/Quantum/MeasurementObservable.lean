module

public import ThomGame.Quantum.MeasurementCalculus

/-! Binary observables extracted from arbitrary projective measurements. -/

@[expose] public section
namespace ThomGame.Quantum

theorem bitSign_norm (a : ZMod 2) : ‖bitSign a‖ = 1 := by
  rcases bit_cases a with rfl | rfl <;> simp [bitSign_zero, bitSign_one]

theorem bitSign_sub_norm_sq (a b : ZMod 2) :
    ‖bitSign a - bitSign b‖ ^ 2 = if a = b then 0 else 4 := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;>
    norm_num [bitSign_zero, bitSign_one]

namespace ProjectiveMeasurement

variable {H A B : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Fintype A] [Fintype B]

noncomputable def observable (P : ProjectiveMeasurement H A) (s : A → ZMod 2) : H →L[ℂ] H :=
  P.eval (fun a => bitSign (s a))

variable (P : ProjectiveMeasurement H A)

theorem observable_selfAdjoint (s : A → ZMod 2) : IsSelfAdjoint (P.observable s) :=
  P.eval_selfAdjoint _ (fun a => bitSign_selfAdjoint (s a))

theorem observable_square (s : A → ZMod 2) : P.observable s * P.observable s = 1 := by
  simp only [observable, P.eval_mul, bitSign_sq, P.eval_one]

theorem observable_commute (s t : A → ZMod 2) :
    Commute (P.observable s) (P.observable t) := P.eval_commute _ _

theorem observable_mul (s t : A → ZMod 2) :
    P.observable s * P.observable t = P.observable (fun a => s a + t a) := by
  simp only [observable, P.eval_mul, bitSign_add]

theorem observable_triple (s t u : A → ZMod 2) :
    P.observable s * P.observable t * P.observable u =
      P.observable (fun a => s a + t a + u a) := by rw [P.observable_mul, P.observable_mul]

theorem observable_norm (s : A → ZMod 2) (ξ : H) : ‖P.observable s ξ‖ = ‖ξ‖ := by
  have h := P.eval_norm_sq (fun a => bitSign (s a)) ξ
  simp only [bitSign_norm, one_pow, one_mul, P.sum_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

theorem observable_sub_sign_norm_sq (s : A → ZMod 2) (b : ZMod 2) (ξ : H) :
    ‖P.observable s ξ - bitSign b • ξ‖ ^ 2 =
      4 * ∑ a, if s a = b then 0 else ‖P.proj a ξ‖ ^ 2 := by
  have h := P.eval_norm_sq (fun a => bitSign (s a) - bitSign b) ξ
  rw [P.eval_sub, P.eval_const] at h
  change ‖P.observable s ξ - bitSign b • ξ‖ ^ 2 = _ at h
  rw [h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [bitSign_sub_norm_sq]
  split <;> simp

theorem observable_cross_commute (Q : ProjectiveMeasurement H B)
    (hc : ∀ a b, Commute (P.proj a) (Q.proj b)) (s : A → ZMod 2) (t : B → ZMod 2) :
    Commute (P.observable s) (Q.observable t) := by
  rw [observable, observable, ← P.joint_eval_left Q hc, ← P.joint_eval_right Q hc]
  exact (P.joint Q hc).eval_commute _ _

theorem observable_difference_norm_sq (Q : ProjectiveMeasurement H B)
    (hc : ∀ a b, Commute (P.proj a) (Q.proj b))
    (s : A → ZMod 2) (t : B → ZMod 2) (ξ : H) :
    ‖P.observable s ξ - Q.observable t ξ‖ ^ 2 =
      4 * ∑ a, ∑ b, if s a = t b then 0 else ‖P.proj a (Q.proj b ξ)‖ ^ 2 := by
  let M := P.joint Q hc
  have h := M.eval_norm_sq (fun ab => bitSign (s ab.1) - bitSign (t ab.2)) ξ
  rw [M.eval_sub] at h
  dsimp only [M] at h
  rw [P.joint_eval_left Q hc (fun a => bitSign (s a)),
    P.joint_eval_right Q hc (fun b => bitSign (t b))] at h
  change ‖P.observable s ξ - Q.observable t ξ‖ ^ 2 = _ at h
  rw [h, Fintype.sum_prod_type]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [bitSign_sub_norm_sq]
  split <;> simp [joint_proj, mul_apply_eq_comp]

end ProjectiveMeasurement
end ThomGame.Quantum
