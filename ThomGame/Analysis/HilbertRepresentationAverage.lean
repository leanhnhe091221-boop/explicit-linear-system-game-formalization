module

public import ThomGame.Analysis.HilbertUnitaryInvariants
public import ThomGame.Analysis.LazyHilbertAverage

/-! The fixed space of a lazy representation average is the invariant space of the generated subgroup. -/

@[expose] public section
namespace ThomGame.Analysis

noncomputable def representationMarkovGapConstant (h : Nat) (c : ℝ) : ℝ :=
  min (1 / 2) (lazyMarkovWeight h * c)

theorem representationMarkovGapConstant_pos (h : Nat) [NeZero h] (c : ℝ) (hc : 0 < c) :
    0 < representationMarkovGapConstant h c :=
  lt_min (by norm_num) (mul_pos (lazyMarkovWeight_pos h) hc)

theorem representationMarkovGapConstant_lt_one (h : Nat) (c : ℝ) :
    representationMarkovGapConstant h c < 1 :=
  (min_le_left _ _).trans_lt (by norm_num)

variable {G H α : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem hilbertUnitaryInvariants_generated_iff (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (K : Subgroup G)
    (s : α → G) (hgen : Subgroup.closure (Set.range s) = K) (ξ : H) :
    ξ ∈ hilbertUnitaryInvariants (ρ.comp K.subtype) ↔ ∀ j, ρ (s j) ξ = ξ := by
  constructor
  · intro hξ j
    have hj : s j ∈ K := by rw [← hgen]; exact Subgroup.subset_closure ⟨j, rfl⟩
    exact hξ ⟨s j, hj⟩
  · intro hfix
    have hle : Subgroup.closure (Set.range s) ≤ hilbertVectorStabilizer ρ ξ := by
      apply (Subgroup.closure_le _).mpr
      rintro g ⟨j, rfl⟩
      exact hfix j
    rw [hgen] at hle
    intro g
    exact hle g.property

theorem hilbertUnitaryInvariants_eq_average_fixed (ρ : G →* (H ≃ₗᵢ[ℂ] H))
    (K : Subgroup G) {h : Nat} [NeZero h] (s : Fin h → G)
    (hgen : Subgroup.closure (Set.range s) = K) :
    hilbertUnitaryInvariants (ρ.comp K.subtype) =
      (lazyHilbertAverage (fun j => ρ (s j))).eqLocus (1 : H →L[ℂ] H) := by
  ext ξ
  rw [hilbertUnitaryInvariants_generated_iff ρ K s hgen ξ]
  change (∀ j, ρ (s j) ξ = ξ) ↔ lazyHilbertAverage (fun j => ρ (s j)) ξ = ξ
  exact (lazyHilbertAverage_fixed_iff _ ξ).symm

end ThomGame.Analysis
