module

public import ThomGame.Analysis.StarProjectionAngleNorm

/-! The energy and exact kernel of a finite sum of orthogonal projection complements. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open scoped BigOperators

variable {ι H : Type*} [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def projectionLaplacian (P : ι → H →L[ℂ] H) : H →L[ℂ] H := ∑ i, (1 - P i)

theorem projectionLaplacian_nonneg (P : ι → H →L[ℂ] H) (hP : ∀ i, IsStarProjection (P i)) :
    0 ≤ projectionLaplacian P := Finset.sum_nonneg (fun i _ => (hP i).one_sub.nonneg)

theorem projectionLaplacian_energy (P : ι → H →L[ℂ] H) (hP : ∀ i, IsStarProjection (P i)) (x : H) :
    (inner ℂ x (projectionLaplacian P x)).re = ∑ i, ‖x - P i x‖ ^ 2 := by
  simp only [projectionLaplacian, sum_apply, inner_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [sub_apply, one_apply_eq_self] using (starProjection_norm_sq (hP i).one_sub x).symm

theorem projectionLaplacian_mem_ker_iff (P : ι → H →L[ℂ] H) (hP : ∀ i, IsStarProjection (P i)) (x : H) :
    x ∈ (projectionLaplacian P).ker ↔ ∀ i, P i x = x := by
  constructor
  · intro hx
    have he := projectionLaplacian_energy P hP x
    change projectionLaplacian P x = 0 at hx
    rw [hx, inner_zero_right, Complex.zero_re] at he
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) =>
      sq_nonneg ‖x - P i x‖)).mp he.symm
    intro i
    have hi : ‖x - P i x‖ = 0 := (sq_eq_zero_iff).mp (hz i (Finset.mem_univ i))
    exact (sub_eq_zero.mp (norm_eq_zero.mp hi)).symm
  · intro hx
    change projectionLaplacian P x = 0
    simp only [projectionLaplacian, sum_apply, sub_apply, one_apply_eq_self, hx, sub_self,
      Finset.sum_const_zero]

theorem projectionLaplacian_ker (P : ι → H →L[ℂ] H) (hP : ∀ i, IsStarProjection (P i)) :
    (projectionLaplacian P).ker = ⨅ i, (P i).eqLocus (1 : H →L[ℂ] H) := by
  ext x
  rw [projectionLaplacian_mem_ker_iff P hP, Submodule.mem_iInf]
  rfl

end ThomGame.Analysis
