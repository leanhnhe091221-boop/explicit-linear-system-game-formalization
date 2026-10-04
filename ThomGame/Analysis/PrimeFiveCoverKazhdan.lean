module

public import ThomGame.Analysis.PrimeFiveCoverRootGap
public import ThomGame.Groups.PrimeFiveCoverRootGeneratingSet
public import Mathlib.Data.Finset.Max

/-!
# An explicit finite Kazhdan set for every actual prime-five cover

The same positive constant works for the union of the three finite root
subgroups, for every coefficient count and every complex Hilbert representation.
-/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open Compressor PrimeFiveRankThreeCover

def primeFiveKazhdanConstant : ℝ := Real.sqrt (2 * primeFiveRootGap / 3)

theorem primeFiveKazhdanConstant_pos : 0 < primeFiveKazhdanConstant := by
  exact Real.sqrt_pos.mpr (div_pos (mul_pos (by norm_num) primeFiveRootGap_pos) (by norm_num))

theorem primeFiveKazhdanConstant_sq : primeFiveKazhdanConstant ^ 2 = 2 * primeFiveRootGap / 3 :=
  Real.sq_sqrt (div_nonneg (mul_nonneg (by norm_num) primeFiveRootGap_pos.le) (by norm_num))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem coverRootGeneratingSet_displacement (d : Nat) (ρ : Cover d →* (H ≃ₗᵢ[ℂ] H))
    (x : H) (hx : x ∈ (hilbertUnitaryInvariants ρ)ᗮ) :
    ∃ g ∈ rootGeneratingSet d, primeFiveKazhdanConstant * ‖x‖ ≤ ‖ρ g x - x‖ := by
  obtain ⟨g, hg, hmax⟩ := Finset.exists_max_image (rootGeneratingSet d)
    (fun g => ‖ρ g x - x‖) (rootGeneratingSet_nonempty d)
  have hmove (c : Axis) (h : rootSubgroup d (cyclicRoot c)) : ‖ρ h.val x - x‖ ≤ ‖ρ g x - x‖ :=
    hmax h.val ((mem_rootGeneratingSet d h.val).mpr ⟨c, h.property⟩)
  have hgap := coverRootLaplacian_displacement_gap d ρ x hx ‖ρ g x - x‖ hmove
  refine ⟨g, hg, (sq_le_sq₀ (mul_nonneg primeFiveKazhdanConstant_pos.le (norm_nonneg _))
    (norm_nonneg _)).mp ?_⟩
  rw [mul_pow, primeFiveKazhdanConstant_sq]
  nlinarith

theorem coverRootGeneratingSet_nonzero_invariant (d : Nat) (ρ : Cover d →* (H ≃ₗᵢ[ℂ] H))
    (x : H) (hx : ‖x‖ = 1)
    (hmove : ∀ g ∈ rootGeneratingSet d, ‖ρ g x - x‖ < primeFiveKazhdanConstant) :
    ∃ v : H, v ≠ 0 ∧ v ∈ hilbertUnitaryInvariants ρ := by
  by_contra h
  have hzero : ∀ v ∈ hilbertUnitaryInvariants ρ, v = (0 : H) := by
    intro v hv
    by_contra hv0
    exact h ⟨v, hv0, hv⟩
  have horth : x ∈ (hilbertUnitaryInvariants ρ)ᗮ := by
    apply (Submodule.mem_orthogonal _ _).mpr
    intro v hv
    rw [hzero v hv, inner_zero_left]
  obtain ⟨g, hg, hbound⟩ := coverRootGeneratingSet_displacement d ρ x horth
  rw [hx, mul_one] at hbound
  exact (not_lt_of_ge hbound) (hmove g hg)

end ThomGame.Analysis
