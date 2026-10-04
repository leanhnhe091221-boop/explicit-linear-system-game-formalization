module

public import ThomGame.Analysis.HilbertRelativeKazhdanBounds
public import ThomGame.Analysis.HilbertInvariantProjection

/-! Distance and uniform subgroup displacement from a relative Kazhdan bound with normal image. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

universe u v w

variable {G : Type v} [Group G] {N : Type w} [Group N]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem hilbertUnitaryInvariants_comp_range (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (ι : N →* G) :
    hilbertUnitaryInvariants (ρ.comp ι) = hilbertUnitaryInvariants (ρ.comp ι.range.subtype) := by
  ext ξ
  constructor
  · intro hξ g
    obtain ⟨n, hn⟩ := g.property
    change ρ g.val ξ = ξ
    rw [← hn]
    exact hξ n
  · intro hξ n
    exact hξ ⟨ι n, ⟨n, rfl⟩⟩

theorem hilbertUnitaryInvariants_comp_stable (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (ι : N →* G)
    [ι.range.Normal] (g : G) (ξ : H) (hξ : ξ ∈ hilbertUnitaryInvariants (ρ.comp ι)) :
    ρ g ξ ∈ hilbertUnitaryInvariants (ρ.comp ι) := by
  rw [hilbertUnitaryInvariants_comp_range] at hξ ⊢
  exact normalInvariants_stable ρ ι.range g ξ hξ

variable [CompleteSpace H]

theorem hilbertRelativeInvariantResidual_displacement_le (ρ : G →* (H ≃ₗᵢ[ℂ] H))
    (ι : N →* G) [ι.range.Normal] (g : G) (ξ : H) :
    ‖ρ g (ξ - (hilbertUnitaryInvariants (ρ.comp ι)).starProjection ξ) -
        (ξ - (hilbertUnitaryInvariants (ρ.comp ι)).starProjection ξ)‖ ≤ ‖ρ g ξ - ξ‖ := by
  let U := hilbertUnitaryInvariants (ρ.comp ι)
  have hcomm := hilbertUnitary_projection_commute ρ U
    (hilbertUnitaryInvariants_comp_stable ρ ι) g ξ
  change ‖ρ g (ξ - U.starProjection ξ) - (ξ - U.starProjection ξ)‖ ≤ _
  rw [map_sub, hcomm]
  have heq : ρ g ξ - U.starProjection (ρ g ξ) - (ξ - U.starProjection ξ) =
      Uᗮ.starProjection (ρ g ξ - ξ) := by
    rw [Submodule.starProjection_orthogonal_val, map_sub]
    abel
  rw [heq]
  exact Submodule.norm_starProjection_apply_le _ _

theorem hilbertRelativeKazhdanBound_distance (ι : N →* G) [ι.range.Normal]
    (S : Finset G) (κ : ℝ) (hκ : 0 < κ) (hS : HilbertRelativeKazhdanBound.{u} ι S κ)
    (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (ξ : H) (ε : ℝ)
    (hmove : ∀ g ∈ S, ‖ρ g ξ - ξ‖ ≤ ε) :
    ‖ξ - (hilbertUnitaryInvariants (ρ.comp ι)).starProjection ξ‖ ≤ ε / κ := by
  obtain ⟨g, hg, hgap⟩ := hS H ρ
    (ξ - (hilbertUnitaryInvariants (ρ.comp ι)).starProjection ξ)
    ((hilbertUnitaryInvariants (ρ.comp ι)).sub_starProjection_mem_orthogonal ξ)
  have hle := hgap.trans ((hilbertRelativeInvariantResidual_displacement_le ρ ι g ξ).trans
    (hmove g hg))
  exact (le_div_iff₀ hκ).mpr (by simpa only [mul_comm] using hle)

theorem hilbertRelativeKazhdanBound_close_invariant (ι : N →* G) [ι.range.Normal]
    (S : Finset G) (κ : ℝ) (hκ : 0 < κ) (hS : HilbertRelativeKazhdanBound.{u} ι S κ)
    (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (ξ : H) (ε : ℝ)
    (hmove : ∀ g ∈ S, ‖ρ g ξ - ξ‖ ≤ ε) :
    ∃ η ∈ hilbertUnitaryInvariants (ρ.comp ι), ‖ξ - η‖ ≤ ε / κ :=
  ⟨_, (hilbertUnitaryInvariants (ρ.comp ι)).starProjection_apply_mem ξ,
    hilbertRelativeKazhdanBound_distance ι S κ hκ hS ρ ξ ε hmove⟩

theorem hilbertRelativeKazhdanBound_uniform_displacement (ι : N →* G) [ι.range.Normal]
    (S : Finset G) (κ : ℝ) (hκ : 0 < κ) (hS : HilbertRelativeKazhdanBound.{u} ι S κ)
    (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (ξ : H) (ε : ℝ)
    (hmove : ∀ g ∈ S, ‖ρ g ξ - ξ‖ ≤ ε) (n : N) :
    ‖ρ (ι n) ξ - ξ‖ ≤ 2 * (ε / κ) := by
  obtain ⟨η, hη, hdist⟩ := hilbertRelativeKazhdanBound_close_invariant ι S κ hκ hS ρ ξ ε hmove
  have hfix : ρ (ι n) η = η := hη n
  have heq : ρ (ι n) ξ - ξ = ρ (ι n) (ξ - η) - (ξ - η) := by
    rw [map_sub, hfix, sub_sub_sub_cancel_right]
  rw [heq]
  calc
    ‖ρ (ι n) (ξ - η) - (ξ - η)‖ ≤ ‖ρ (ι n) (ξ - η)‖ + ‖ξ - η‖ := norm_sub_le _ _
    _ = 2 * ‖ξ - η‖ := by rw [(ρ (ι n)).norm_map]; ring
    _ ≤ 2 * (ε / κ) := mul_le_mul_of_nonneg_left hdist (by norm_num)

end ThomGame.Analysis
