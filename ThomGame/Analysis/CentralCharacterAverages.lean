module

public import ThomGame.Analysis.FiniteCharacterDecomposition
public import ThomGame.Analysis.CentralCharacterAngleBound

/-! Central character spaces are preserved by subgroup averaging. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem finiteSubgroupAverage_central_commute (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (A : Subgroup G) [Finite A]
    (z : G) (hz : z ∈ Subgroup.center G) (x : H) :
    finiteSubgroupAverage ρ A (ρ z x) = ρ z (finiteSubgroupAverage ρ A x) := by
  symm
  apply finiteSubgroupAverage_commute ρ A (ρ z : H →L[ℂ] H)
  intro a y
  change ρ z (ρ a.val y) = ρ a.val (ρ z y)
  rw [← hilbertUnitary_apply_mul, ← hilbertUnitary_apply_mul,
    (Subgroup.mem_center_iff.mp hz a.val).symm]

theorem finiteSubgroupAverage_preserves_central_character
    (hC : _root_.commutator G ≤ Subgroup.center G) (ρ : G →* (H ≃ₗᵢ[ℂ] H))
    (κ : _root_.commutator G →* ℂ) (A : Subgroup G) [Finite A]
    (x : H) (hx : ∀ z : _root_.commutator G, ρ z.val x = κ z • x) :
    ∀ z : _root_.commutator G, ρ z.val (finiteSubgroupAverage ρ A x) =
      κ z • finiteSubgroupAverage ρ A x := by
  intro z
  rw [← finiteSubgroupAverage_central_commute ρ A z.val (hC z.property), hx, map_smul]

theorem hilbertUnitaryInvariants_of_sup (ρ : G →* (H ≃ₗᵢ[ℂ] H))
    (A B : Subgroup G) (hgen : A ⊔ B = ⊤) (x : H)
    (hA : x ∈ hilbertUnitaryInvariants (ρ.comp A.subtype))
    (hB : x ∈ hilbertUnitaryInvariants (ρ.comp B.subtype)) : x ∈ hilbertUnitaryInvariants ρ := by
  have hle : A ⊔ B ≤ hilbertVectorStabilizer ρ x := by
    apply sup_le
    · intro a ha
      exact hA ⟨a, ha⟩
    · intro b hb
      exact hB ⟨b, hb⟩
  rw [hgen] at hle
  intro g
  exact hle (Subgroup.mem_top g)

theorem finiteAverage_trivial_character_invariant
    (hC : _root_.commutator G ≤ Subgroup.center G) (ρ : G →* (H ≃ₗᵢ[ℂ] H))
    (A B : Subgroup G) [Finite B] (hgen : A ⊔ B = ⊤) (x : H)
    (hx : ∀ z : _root_.commutator G, ρ z.val x = x)
    (hA : x ∈ hilbertUnitaryInvariants (ρ.comp A.subtype)) :
    finiteSubgroupAverage ρ B x ∈ hilbertUnitaryInvariants ρ := by
  apply hilbertUnitaryInvariants_of_sup ρ A B hgen
  · let := Fintype.ofFinite B
    change finiteUnitaryAverage (ρ.comp B.subtype) x ∈ _
    rw [finiteUnitaryAverage_apply]
    apply Submodule.smul_mem
    apply Submodule.sum_mem
    intro b _ a
    change ρ a.val (ρ b.val x) = ρ b.val x
    simpa only [MonoidHom.one_apply, one_smul] using
      centralCharacter_translate_eigen hC ρ 1 x (by simpa only [MonoidHom.one_apply, one_smul] using hx)
        a.val b.val (hA a)
  · exact finiteSubgroupAverage_invariant ρ B x

end ThomGame.Analysis
