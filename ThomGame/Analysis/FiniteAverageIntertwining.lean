module

public import ThomGame.Analysis.FiniteSubgroupAverage

/-! Right invariance and eigenvector cancellation for actual finite subgroup averages. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open scoped BigOperators

variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem finiteUnitaryAverage_apply_unitary [Fintype G] (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (g : G) (x : H) :
    finiteUnitaryAverage ρ (ρ g x) = finiteUnitaryAverage ρ x := by
  rw [finiteUnitaryAverage_apply, finiteUnitaryAverage_apply]
  simp only [← hilbertUnitary_apply_mul]
  congr 1
  simpa using Equiv.sum_comp (Equiv.mulRight g) (fun a => ρ a x)

theorem finiteUnitaryAverage_commute [Fintype G] (ρ : G →* (H ≃ₗᵢ[ℂ] H))
    (T : H →L[ℂ] H) (hT : ∀ g x, T (ρ g x) = ρ g (T x)) (x : H) :
    T (finiteUnitaryAverage ρ x) = finiteUnitaryAverage ρ (T x) := by
  simp only [finiteUnitaryAverage_apply, map_smul, map_sum, hT]

theorem finiteSubgroupAverage_apply_unitary (ρ : G →* (H ≃ₗᵢ[ℂ] H))
    (A : Subgroup G) [Finite A] (a : A) (x : H) :
    finiteSubgroupAverage ρ A (ρ a.val x) = finiteSubgroupAverage ρ A x := by
  let := Fintype.ofFinite A
  exact finiteUnitaryAverage_apply_unitary (ρ.comp A.subtype) a x

theorem finiteSubgroupAverage_commute (ρ : G →* (H ≃ₗᵢ[ℂ] H))
    (A : Subgroup G) [Finite A] (T : H →L[ℂ] H) (hT : ∀ a : A, ∀ x, T (ρ a.val x) = ρ a.val (T x))
    (x : H) : T (finiteSubgroupAverage ρ A x) = finiteSubgroupAverage ρ A (T x) := by
  let := Fintype.ofFinite A
  exact finiteUnitaryAverage_commute (ρ.comp A.subtype) T hT x

theorem finiteSubgroupAverage_eq_zero_of_eigen (ρ : G →* (H ≃ₗᵢ[ℂ] H))
    (A : Subgroup G) [Finite A] (a : A) (x : H) (α : ℂ) (hα : α ≠ 1)
    (hx : ρ a.val x = α • x) : finiteSubgroupAverage ρ A x = 0 := by
  have h := finiteSubgroupAverage_apply_unitary ρ A a x
  rw [hx, map_smul] at h
  have hz : (α - 1) • finiteSubgroupAverage ρ A x = 0 := by rw [sub_smul, one_smul, h, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hα)

theorem finiteSubgroupAverage_inner_fixed (ρ : G →* (H ≃ₗᵢ[ℂ] H))
    (A : Subgroup G) [Finite A] (x : H)
    (hx : x ∈ hilbertUnitaryInvariants (ρ.comp A.subtype)) (y : H) :
    inner ℂ x (finiteSubgroupAverage ρ A y) = inner ℂ x y := by
  let := Fintype.ofFinite A
  exact finiteUnitaryAverage_inner_fixed (ρ.comp A.subtype) x hx y

theorem finiteSubgroupAverage_norm_sq (ρ : G →* (H ≃ₗᵢ[ℂ] H))
    (A : Subgroup G) [Finite A] (x : H) :
    ‖finiteSubgroupAverage ρ A x‖ ^ 2 = (inner ℂ x (finiteSubgroupAverage ρ A x)).re := by
  calc
    _ = (inner ℂ (finiteSubgroupAverage ρ A x) (finiteSubgroupAverage ρ A x)).re :=
      norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ = (inner ℂ (finiteSubgroupAverage ρ A x) x).re := congrArg Complex.re
      (finiteSubgroupAverage_inner_fixed ρ A _ (finiteSubgroupAverage_invariant ρ A x) x)
    _ = _ := inner_re_symm (𝕜 := ℂ) _ _

end ThomGame.Analysis
