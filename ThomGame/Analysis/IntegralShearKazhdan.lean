module

public import ThomGame.Analysis.IntegralShearVertexDisplacement
public import ThomGame.Analysis.HilbertNonInvariantRepresentation
public import ThomGame.Analysis.HilbertKazhdanBounds

/-! An unconditional finite Hilbert Kazhdan set for the actual integral shear presentation. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

universe u

open Compressor IntegralShear

def integralShearKazhdanSet : Finset ShearGroup := by
  classical
  exact Finset.univ.image of

def integralShearKazhdanConstant : ℝ := 1 / 2401

theorem integralShearKazhdanConstant_pos : 0 < integralShearKazhdanConstant := by
  norm_num [integralShearKazhdanConstant]

theorem of_mem_integralShearKazhdanSet (r : Root) : of r ∈ integralShearKazhdanSet := by
  classical
  exact Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩

theorem integralShear_orthogonal_norm_le
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (ξ : H) (hξ : ξ ∈ (hilbertUnitaryInvariants ρ)ᗮ)
    (ε : ℝ) (hmove : ∀ s : Root, ‖ρ (of s) ξ - ξ‖ ≤ ε) : ‖ξ‖ ≤ 2400 * ε := by
  have h := integralShear_no_invariants_norm_le (hilbertNonInvariantRepresentation ρ)
    (hilbertNonInvariantRepresentation_invariants ρ) ⟨ξ, hξ⟩ ε (fun r => hmove r)
  exact h

theorem integralShear_hilbertKazhdanBound :
    HilbertKazhdanBound.{u} integralShearKazhdanSet integralShearKazhdanConstant := by
  intro H _ _ _ ρ ξ hξ
  by_contra h
  have hnz : ξ ≠ 0 := by
    intro hz
    exact h ⟨of root12, of_mem_integralShearKazhdanSet root12, by simp [hz]⟩
  have hmove (r : Root) : ‖ρ (of r) ξ - ξ‖ ≤ integralShearKazhdanConstant * ‖ξ‖ := by
    apply le_of_lt
    apply lt_of_not_ge
    intro hr
    exact h ⟨of r, of_mem_integralShearKazhdanSet r, hr⟩
  have hnorm := integralShear_orthogonal_norm_le ρ ξ hξ (integralShearKazhdanConstant * ‖ξ‖) hmove
  have hpos := norm_pos_iff.mpr hnz
  unfold integralShearKazhdanConstant at hnorm
  linarith

theorem integralShear_hasFiniteHilbertKazhdanSet : HasFiniteHilbertKazhdanSet.{u} ShearGroup :=
  ⟨integralShearKazhdanSet, integralShearKazhdanConstant,
    integralShearKazhdanConstant_pos, integralShear_hilbertKazhdanBound⟩

end ThomGame.Analysis
