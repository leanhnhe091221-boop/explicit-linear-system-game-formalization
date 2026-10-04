module

public import ThomGame.Analysis.IntegralShearRootAngles
public import ThomGame.Analysis.IntegerHeisenbergLocalCodistance

/-! The four-edge local bound specialized to the genuine integer root pairs. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open Compressor IntegralShear

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem rootPairSubgroup_invariants_eq (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (r : Root) :
    hilbertUnitaryInvariants (ρ.comp (rootPairSubgroup r).subtype) =
      hilbertUnitaryInvariants (ρ.comp (rootSubgroup r).subtype) ⊓
        hilbertUnitaryInvariants (ρ.comp (rootSubgroup (right r)).subtype) := by
  ext ξ
  constructor
  · intro hξ
    have hleft : rootSubgroup r ≤ rootPairSubgroup r := le_sup_left
    have hright : rootSubgroup (right r) ≤ rootPairSubgroup r := le_sup_right
    exact ⟨fun g => hξ ⟨g.val, hleft g.property⟩,
      fun g => hξ ⟨g.val, hright g.property⟩⟩
  · rintro ⟨h₁, h₂⟩ g
    have hle : rootPairSubgroup r ≤ hilbertVectorStabilizer ρ ξ :=
      sup_le (fun x hx => h₁ ⟨x, hx⟩) (fun x hx => h₂ ⟨x, hx⟩)
    exact hle g.property

variable [CompleteSpace H]

theorem integralRootPair_four_sum_sq_le (ρ : ShearGroup →* (H ≃ₗᵢ[ℂ] H)) (r : Root)
    (hpair : hilbertUnitaryInvariants (ρ.comp (rootPairSubgroup r).subtype) = ⊥)
    (a b c d : H)
    (ha : a ∈ hilbertUnitaryInvariants (ρ.comp (rootSubgroup (right r)).subtype))
    (haZ : a ∈ hilbertUnitaryInvariants (ρ.comp (rootSubgroup (across r)).subtype))
    (hb : b ∈ hilbertUnitaryInvariants (ρ.comp (rootSubgroup r).subtype))
    (hbZ : b ∈ hilbertUnitaryInvariants (ρ.comp (rootSubgroup (across r)).subtype))
    (hc : c ∈ hilbertUnitaryInvariants (ρ.comp (rootSubgroup (right r)).subtype))
    (hd : d ∈ hilbertUnitaryInvariants (ρ.comp (rootSubgroup r).subtype)) :
    ‖a + b + c + d‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2) := by
  have hXZ : Commute (ρ (of (right r))) (ρ (of (across r))) :=
    (of_commute (right r) (across r)
      ((show ∀ s : Root, separated (right s) (across s) from by decide +kernel) r)).map ρ
  have hcommon : ∀ w : H, ρ (of (right r)) w = w → ρ (of r) w = w → w = 0 := by
    intro w hwX hwY
    have hw : w ∈ hilbertUnitaryInvariants (ρ.comp (rootPairSubgroup r).subtype) := by
      rw [rootPairSubgroup_invariants_eq, rootSubgroup_invariants_eq, rootSubgroup_invariants_eq]
      exact ⟨hwY, hwX⟩
    rwa [hpair, Submodule.mem_bot] at hw
  rw [rootSubgroup_invariants_eq] at ha haZ hb hbZ hc hd
  exact unitaryHeisenberg_four_sum_sq_le (ρ (of (right r))) (ρ (of r)) (ρ (of (across r)))
    (rootPair_unitary_heisenberg_relation ρ r) (rootPair_unitary_center_commute ρ r) hXZ hcommon
    a b c d ha haZ hb hbZ hc hd

end ThomGame.Analysis
