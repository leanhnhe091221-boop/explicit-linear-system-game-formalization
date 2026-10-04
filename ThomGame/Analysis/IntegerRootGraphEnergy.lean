module

public import ThomGame.Analysis.IntegerRootGraphOperators
public import ThomGame.Analysis.PositiveOperatorEstimates

/-! The exact edge energy and positivity of the six-root graph Laplacian. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis.IntegerRootGraph

open Compressor ThomGame.IntegerRootGraph
open scoped BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def edgeEnergy (f : VertexHilbert H) : ℝ :=
  (1 / 2 : ℝ) * ∑ r : Root, ∑ i : Fin 4, ‖f r - f (neighbor r i)‖ ^ 2

omit [InnerProductSpace ℂ H] in
theorem edgeEnergy_nonneg (f : VertexHilbert H) : 0 ≤ edgeEnergy f := by
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem laplacian_energy_expanded (f : VertexHilbert H) :
    (inner ℂ f (laplacian f)).re =
      4 * (∑ r : Root, ‖f r‖ ^ 2) - ∑ r : Root, ∑ i : Fin 4, (inner ℂ (f r) (f (neighbor r i))).re := by
  have h (r : Root) : (inner ℂ (f r) (laplacian f r)).re =
      4 * ‖f r‖ ^ 2 - ∑ i : Fin 4, (inner ℂ (f r) (f (neighbor r i))).re := by
    rw [laplacian_apply, inner_sub_right, inner_smul_right, inner_sum, Complex.sub_re, Complex.re_sum,
      inner_self_eq_norm_sq_to_K]
    norm_num [Complex.mul_re]
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  rw [PiLp.inner_apply, Complex.re_sum]
  simp_rw [h]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem laplacian_energy (f : VertexHilbert H) : (inner ℂ f (laplacian f)).re = edgeEnergy f := by
  have hsource : (∑ r : Root, ∑ _i : Fin 4, ‖f r‖ ^ 2) = 4 * (∑ r : Root, ‖f r‖ ^ 2) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    norm_num
  have htarget : (∑ r : Root, ∑ i : Fin 4, ‖f (neighbor r i)‖ ^ 2) = 4 * (∑ r : Root, ‖f r‖ ^ 2) := by
    rw [Finset.sum_comm]
    calc
      (∑ i : Fin 4, ∑ r : Root, ‖f (neighbor r i)‖ ^ 2) = ∑ _i : Fin 4, ∑ r : Root, ‖f r‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        exact sum_neighbors_reindex (fun r => ‖f r‖ ^ 2) i
      _ = _ := by simp
  rw [laplacian_energy_expanded, edgeEnergy]
  simp_rw [norm_sub_sq (𝕜 := ℂ), RCLike.re_to_complex]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hsource, htarget]
  ring

theorem laplacian_symmetric : (laplacian : VertexHilbert H →L[ℂ] VertexHilbert H).IsSymmetric := by
  intro f g
  rw [laplacian_operator_formula]
  change inner ℂ ((5 : ℂ) • f + opposite f - total f) g =
    inner ℂ f ((5 : ℂ) • g + opposite g - total g)
  simp [inner_sub_left, inner_add_left, inner_smul_left, inner_sub_right, inner_add_right,
    inner_smul_right, opposite_inner, total_inner, map_ofNat]

theorem laplacian_nonneg : (0 : VertexHilbert H →L[ℂ] VertexHilbert H) ≤ laplacian := by
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  refine ⟨laplacian_symmetric, ?_⟩
  intro f
  change 0 ≤ RCLike.re (inner ℂ (laplacian f) f)
  simpa only [inner_re_symm, RCLike.re_to_complex, laplacian_energy] using edgeEnergy_nonneg f

end ThomGame.Analysis.IntegerRootGraph
