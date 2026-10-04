module

public import ThomGame.Analysis.HilbertKazhdanBounds
public import ThomGame.Analysis.HilbertInvariantProjection

/-!
# Finite Kazhdan bounds for normal extensions

A group mapping onto the quotient acts on the actual normal-invariant
Hilbert subspace. The orthogonal residual is controlled by the normal
subgroup. Both estimates use the displacement of the original vector.
-/

@[expose] public noncomputable section
namespace ThomGame.Analysis

universe u v w

variable {G : Type v} [Group G] {B : Type w} [Group B]

def normalExtensionKazhdanSet (N : Subgroup G) (f : B →* G)
    (SN : Finset N) (SB : Finset B) : Finset G := by
  classical
  exact SN.image N.subtype ∪ SB.image f

def normalExtensionKazhdanConstant (a b : ℝ) : ℝ := min a b / 2

theorem normalExtensionKazhdanConstant_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < normalExtensionKazhdanConstant a b := div_pos (lt_min ha hb) (by norm_num)

theorem hilbertKazhdanBound_normalExtension (N : Subgroup G) [N.Normal] (f : B →* G)
    (hf : Function.Surjective ((QuotientGroup.mk' N).comp f))
    (SN : Finset N) (SB : Finset B) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hN : HilbertKazhdanBound.{u} SN a) (hB : HilbertKazhdanBound.{u} SB b) :
    HilbertKazhdanBound.{u} (normalExtensionKazhdanSet N f SN SB)
      (normalExtensionKazhdanConstant a b) := by
  classical
  intro H _ _ _ ρ x hx
  let y := normalInvariantVector ρ N x
  let z := x - y.val
  let β := (normalQuotientRepresentation ρ N).comp ((QuotientGroup.mk' N).comp f)
  have hy : y ∈ (hilbertUnitaryInvariants β)ᗮ := by
    rw [hilbertUnitaryInvariants_comp_surjective _ _ hf]
    exact normalInvariantVector_orthogonal ρ N x hx
  obtain ⟨n, hn, hnmove⟩ := hN H (ρ.comp N.subtype) z (normalInvariantResidual_orthogonal ρ N x)
  obtain ⟨g, hg, hgmove⟩ := hB _ β y hy
  change a * ‖z‖ ≤ ‖ρ n.val z - z‖ at hnmove
  have hnmove' : a * ‖z‖ ≤ ‖ρ n.val x - x‖ := by
    simpa only [z, y, normalInvariantResidual_displacement] using hnmove
  have hgmove' : b * ‖y.val‖ ≤ ‖ρ (f g) x - x‖ := by
    change b * ‖y.val‖ ≤ ‖ρ (f g) y.val - y.val‖ at hgmove
    exact hgmove.trans (normalInvariantVector_displacement_le ρ N (f g) x)
  have hnE : n.val ∈ normalExtensionKazhdanSet N f SN SB :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨n, hn, rfl⟩)
  have hgE : f g ∈ normalExtensionKazhdanSet N f SN SB :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
  by_contra h
  push Not at h
  have hnl := hnmove'.trans_lt (h n.val hnE)
  have hgl := hgmove'.trans_lt (h (f g) hgE)
  have htriangle : ‖x‖ ≤ ‖z‖ + ‖y.val‖ := by
    simpa only [z, sub_add_cancel] using norm_add_le z y.val
  have hsum : min a b * ‖x‖ ≤ a * ‖z‖ + b * ‖y.val‖ := by
    calc
      min a b * ‖x‖ ≤ min a b * (‖z‖ + ‖y.val‖) :=
        mul_le_mul_of_nonneg_left htriangle (le_of_lt (lt_min ha hb))
      _ = min a b * ‖z‖ + min a b * ‖y.val‖ := mul_add _ _ _
      _ ≤ a * ‖z‖ + b * ‖y.val‖ := add_le_add
        (mul_le_mul_of_nonneg_right (min_le_left a b) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (min_le_right a b) (norm_nonneg _))
  unfold normalExtensionKazhdanConstant at hnl hgl
  linarith

theorem hasFiniteHilbertKazhdanSet_normalExtension (N : Subgroup G) [N.Normal] (f : B →* G)
    (hf : Function.Surjective ((QuotientGroup.mk' N).comp f))
    (hN : HasFiniteHilbertKazhdanSet.{u} N) (hB : HasFiniteHilbertKazhdanSet.{u} B) :
    HasFiniteHilbertKazhdanSet.{u} G := by
  obtain ⟨SN, a, ha, hSN⟩ := hN
  obtain ⟨SB, b, hb, hSB⟩ := hB
  exact ⟨normalExtensionKazhdanSet N f SN SB, normalExtensionKazhdanConstant a b,
    normalExtensionKazhdanConstant_pos ha hb,
    hilbertKazhdanBound_normalExtension N f hf SN SB a b ha hb hSN hSB⟩

end ThomGame.Analysis
