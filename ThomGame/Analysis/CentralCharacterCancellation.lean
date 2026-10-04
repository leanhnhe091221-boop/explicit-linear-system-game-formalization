module

public import ThomGame.Analysis.FiniteAverageIntertwining
public import ThomGame.Groups.CentralCommutatorCrossGeneration

/-! Character cancellation outside the actual commutator annihilator. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open scoped commutatorElement

variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem centralCharacter_translate_eigen (hC : _root_.commutator G ≤ Subgroup.center G)
    (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (κ : _root_.commutator G →* ℂ)
    (x : H) (hx : ∀ z : _root_.commutator G, ρ z.val x = κ z • x)
    (a b : G) (ha : ρ a x = x) :
    ρ a (ρ b x) = κ (commutatorElementIn a b) • ρ b x := by
  have hc : Commute b ⁅a, b⁆ := Subgroup.mem_center_iff.mp (hC (commutatorElementIn a b).property) b
  have hab : a * b = b * (⁅a, b⁆ * a) := by
    rw [← mul_assoc, hc.eq]
    simp only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one]
  rw [← hilbertUnitary_apply_mul, hab, hilbertUnitary_apply_mul,
    hilbertUnitary_apply_mul, ha]
  change ρ b (ρ (commutatorElementIn a b).val x) = _
  rw [hx, map_smul]

theorem finiteAverage_translate_vanishes (hC : _root_.commutator G ≤ Subgroup.center G)
    (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (κ : _root_.commutator G →* ℂ)
    (A B : Subgroup G) [Finite A] (x : H)
    (hx : ∀ z : _root_.commutator G, ρ z.val x = κ z • x)
    (hA : x ∈ hilbertUnitaryInvariants (ρ.comp A.subtype)) (b : B)
    (hb : b ∉ commutatorCharacterAnnihilator hC κ A B) :
    finiteSubgroupAverage ρ A (ρ b.val x) = 0 := by
  rw [mem_commutatorCharacterAnnihilator] at hb
  push Not at hb
  obtain ⟨a, ha⟩ := hb
  exact finiteSubgroupAverage_eq_zero_of_eigen ρ A a _ _ ha
    (centralCharacter_translate_eigen hC ρ κ x hx a.val b.val (hA a))

theorem finiteAverage_translate_fixed (hC : _root_.commutator G ≤ Subgroup.center G)
    (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (κ : _root_.commutator G →* ℂ)
    (A B : Subgroup G) [Finite A] (x : H)
    (hx : ∀ z : _root_.commutator G, ρ z.val x = κ z • x)
    (hA : x ∈ hilbertUnitaryInvariants (ρ.comp A.subtype)) (b : B)
    (hb : b ∈ commutatorCharacterAnnihilator hC κ A B) :
    finiteSubgroupAverage ρ A (ρ b.val x) = ρ b.val x := by
  apply finiteSubgroupAverage_of_invariant
  intro a
  change ρ a.val (ρ b.val x) = ρ b.val x
  rw [centralCharacter_translate_eigen hC ρ κ x hx a.val b.val (hA a),
    (mem_commutatorCharacterAnnihilator hC κ A B b).mp hb a, one_smul]

end ThomGame.Analysis
