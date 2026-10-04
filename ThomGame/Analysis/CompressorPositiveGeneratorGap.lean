module

public import ThomGame.Analysis.CompressorFiniteKazhdanSets
public import ThomGame.Analysis.HilbertGeneratorWordEstimates
public import ThomGame.Groups.CompressorGeneratingTuples

/-!
# An unconditional Hilbert gap for the specified 24 generators of H

The finite word bound depends only on the actual group and generating
tuple. Consequently the positive constant is independent of both the
Hilbert space and the unitary representation.
-/

@[expose] public noncomputable section
namespace ThomGame.Compressor

open Analysis
open scoped BigOperators

def positiveKazhdanSetInQ : Finset GroupQ := by
  classical
  exact positiveKazhdanSet.image (fun g : positiveSubgroup => g.val)

theorem positiveKazhdanSetInQ_mem_closure (g : GroupQ) (hg : g ∈ positiveKazhdanSetInQ) :
    g ∈ Subgroup.closure (Set.range positiveGeneratorTuple) := by
  classical
  obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp hg
  rw [positiveGeneratorTuple_generates]
  exact h.property

def positiveGeneratorWordConstant : Nat :=
  finiteSetWordConstant (Set.range positiveGeneratorTuple) positiveKazhdanSetInQ positiveKazhdanSetInQ_mem_closure

theorem positiveGeneratorWordConstant_pos : 0 < positiveGeneratorWordConstant :=
  finiteSetWordConstant_pos _ _ _

def positiveGeneratorKazhdanConstant : ℝ := primeFiveKazhdanConstant / positiveGeneratorWordConstant

theorem positiveGeneratorKazhdanConstant_pos : 0 < positiveGeneratorKazhdanConstant :=
  div_pos primeFiveKazhdanConstant_pos (Nat.cast_pos.mpr positiveGeneratorWordConstant_pos)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem positiveGeneratorTuple_displacement (ρ : GroupQ →* (H ≃ₗᵢ[ℂ] H)) (x : H)
    (hx : x ∈ (hilbertUnitaryInvariants (ρ.comp positiveSubgroup.subtype))ᗮ) :
    ∃ j : Fin 24, positiveGeneratorKazhdanConstant * ‖x‖ ≤ ‖ρ (positiveGeneratorTuple j) x - x‖ := by
  classical
  obtain ⟨j, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 24))
    (fun i => ‖ρ (positiveGeneratorTuple i) x - x‖) ⟨0, Finset.mem_univ 0⟩
  obtain ⟨g, hg, hgap⟩ := positiveKazhdanSet_displacement (ρ.comp positiveSubgroup.subtype) x hx
  have hmove : ∀ s ∈ Set.range positiveGeneratorTuple, ‖ρ s x - x‖ ≤ ‖ρ (positiveGeneratorTuple j) x - x‖ := by
    rintro s ⟨i, rfl⟩
    exact hmax i (Finset.mem_univ i)
  have hbound := finiteSetWordConstant_displacement (Set.range positiveGeneratorTuple)
    positiveKazhdanSetInQ positiveKazhdanSetInQ_mem_closure ρ x ‖ρ (positiveGeneratorTuple j) x - x‖
    (norm_nonneg _) hmove g.val (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
  have hC : (0 : ℝ) < positiveGeneratorWordConstant := Nat.cast_pos.mpr positiveGeneratorWordConstant_pos
  change primeFiveKazhdanConstant * ‖x‖ ≤ ‖ρ g.val x - x‖ at hgap
  change ‖ρ g.val x - x‖ ≤ (positiveGeneratorWordConstant : ℝ) * ‖ρ (positiveGeneratorTuple j) x - x‖ at hbound
  have hfinal : primeFiveKazhdanConstant * ‖x‖ / positiveGeneratorWordConstant ≤ ‖ρ (positiveGeneratorTuple j) x - x‖ := by
    apply (div_le_iff₀ hC).mpr
    exact (hgap.trans hbound).trans_eq (mul_comm _ _)
  exact ⟨j, by simpa only [positiveGeneratorKazhdanConstant, div_mul_eq_mul_div] using hfinal⟩

theorem positiveGeneratorTuple_energy_gap (ρ : GroupQ →* (H ≃ₗᵢ[ℂ] H)) (x : H)
    (hx : x ∈ (hilbertUnitaryInvariants (ρ.comp positiveSubgroup.subtype))ᗮ) :
    positiveGeneratorKazhdanConstant ^ 2 * ‖x‖ ^ 2 ≤ ∑ j : Fin 24, ‖ρ (positiveGeneratorTuple j) x - x‖ ^ 2 := by
  obtain ⟨j, hj⟩ := positiveGeneratorTuple_displacement ρ x hx
  have hs := pow_le_pow_left₀ (mul_nonneg positiveGeneratorKazhdanConstant_pos.le (norm_nonneg _)) hj 2
  rw [mul_pow] at hs
  exact hs.trans (Finset.single_le_sum (fun i _ => sq_nonneg ‖ρ (positiveGeneratorTuple i) x - x‖)
    (Finset.mem_univ j))

end ThomGame.Compressor
