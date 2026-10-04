module

public import ThomGame.Analysis.HilbertKazhdanBounds
public import ThomGame.Analysis.HilbertGeneratorWordEstimates

/-! Transfer a finite Kazhdan bound to any actual finite generating tuple. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

universe u v w

variable {G : Type v} [Group G] {ι : Type w}

theorem generatingTuple_mem_closure (s : ι → G) (hs : Subgroup.closure (Set.range s) = ⊤)
    (S : Finset G) (g : G) (_hg : g ∈ S) : g ∈ Subgroup.closure (Set.range s) := by
  rw [hs]
  trivial

def generatingTupleWordConstant (s : ι → G) (hs : Subgroup.closure (Set.range s) = ⊤)
    (S : Finset G) : Nat :=
  finiteSetWordConstant (Set.range s) S (generatingTuple_mem_closure s hs S)

theorem generatingTupleWordConstant_pos (s : ι → G) (hs : Subgroup.closure (Set.range s) = ⊤)
    (S : Finset G) : 0 < generatingTupleWordConstant s hs S := finiteSetWordConstant_pos _ _ _

def generatingTupleKazhdanConstant (s : ι → G) (hs : Subgroup.closure (Set.range s) = ⊤)
    (S : Finset G) (κ : ℝ) : ℝ := κ / generatingTupleWordConstant s hs S

theorem generatingTupleKazhdanConstant_pos (s : ι → G) (hs : Subgroup.closure (Set.range s) = ⊤)
    (S : Finset G) {κ : ℝ} (hκ : 0 < κ) : 0 < generatingTupleKazhdanConstant s hs S κ :=
  div_pos hκ (Nat.cast_pos.mpr (generatingTupleWordConstant_pos s hs S))

variable [Fintype ι] [Nonempty ι]

theorem generatingTuple_displacement_of_kazhdanBound (s : ι → G)
    (hs : Subgroup.closure (Set.range s) = ⊤) (S : Finset G) (κ : ℝ)
    (hS : HilbertKazhdanBound.{u} S κ)
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (x : H) (hx : x ∈ (hilbertUnitaryInvariants ρ)ᗮ) :
    ∃ j : ι, generatingTupleKazhdanConstant s hs S κ * ‖x‖ ≤ ‖ρ (s j) x - x‖ := by
  classical
  obtain ⟨j, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset ι)
    (fun i => ‖ρ (s i) x - x‖) Finset.univ_nonempty
  obtain ⟨g, hg, hgap⟩ := hS H ρ x hx
  have hmove : ∀ t ∈ Set.range s, ‖ρ t x - x‖ ≤ ‖ρ (s j) x - x‖ := by
    rintro t ⟨i, rfl⟩
    exact hmax i (Finset.mem_univ i)
  have hbound := finiteSetWordConstant_displacement (Set.range s) S
    (generatingTuple_mem_closure s hs S) ρ x ‖ρ (s j) x - x‖ (norm_nonneg _) hmove g hg
  have hC : (0 : ℝ) < generatingTupleWordConstant s hs S :=
    Nat.cast_pos.mpr (generatingTupleWordConstant_pos s hs S)
  have hfinal : κ * ‖x‖ / generatingTupleWordConstant s hs S ≤ ‖ρ (s j) x - x‖ := by
    apply (div_le_iff₀ hC).mpr
    exact (hgap.trans hbound).trans_eq (mul_comm _ _)
  exact ⟨j, by simpa only [generatingTupleKazhdanConstant, div_mul_eq_mul_div] using hfinal⟩

theorem generatingTuple_energy_of_kazhdanBound (s : ι → G)
    (hs : Subgroup.closure (Set.range s) = ⊤) (S : Finset G) (κ : ℝ) (hκ : 0 < κ)
    (hS : HilbertKazhdanBound.{u} S κ)
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (x : H) (hx : x ∈ (hilbertUnitaryInvariants ρ)ᗮ) :
    generatingTupleKazhdanConstant s hs S κ ^ 2 * ‖x‖ ^ 2 ≤ ∑ j, ‖ρ (s j) x - x‖ ^ 2 := by
  obtain ⟨j, hj⟩ := generatingTuple_displacement_of_kazhdanBound s hs S κ hS ρ x hx
  have hp := generatingTupleKazhdanConstant_pos s hs S hκ
  have hsq := pow_le_pow_left₀ (mul_nonneg hp.le (norm_nonneg _)) hj 2
  rw [mul_pow] at hsq
  exact hsq.trans (Finset.single_le_sum (fun i _ => sq_nonneg ‖ρ (s i) x - x‖) (Finset.mem_univ j))

theorem exists_generatingTuple_energy_gap (s : ι → G) (hs : Subgroup.closure (Set.range s) = ⊤)
    (hG : HasFiniteHilbertKazhdanSet.{u} G) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
        ∀ (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (x : H), x ∈ (hilbertUnitaryInvariants ρ)ᗮ →
          c * ‖x‖ ^ 2 ≤ ∑ j, ‖ρ (s j) x - x‖ ^ 2 := by
  obtain ⟨S, κ, hκ, hS⟩ := hG
  refine ⟨generatingTupleKazhdanConstant s hs S κ ^ 2,
    sq_pos_of_pos (generatingTupleKazhdanConstant_pos s hs S hκ), ?_⟩
  intro H _ _ _ ρ x hx
  exact generatingTuple_energy_of_kazhdanBound s hs S κ hκ hS ρ x hx

end ThomGame.Analysis
