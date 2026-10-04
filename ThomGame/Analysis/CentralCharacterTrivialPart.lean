module

public import ThomGame.Analysis.CentralCharacterAverages

/-! The trivial commutator character gives precisely the global invariant projection. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem eq_zero_of_character_and_global_invariant (ρ : G →* (H ≃ₗᵢ[ℂ] H))
    (κ : _root_.commutator G →* ℂ) (hκ : κ ≠ 1) (x : H)
    (hx : ∀ z : _root_.commutator G, ρ z.val x = κ z • x)
    (hfix : x ∈ hilbertUnitaryInvariants ρ) : x = 0 := by
  have hex : ∃ z, κ z ≠ 1 := by
    by_contra! h
    exact hκ (MonoidHom.ext h)
  obtain ⟨z, hz⟩ := hex
  have heq : κ z • x = x := (hx z).symm.trans (hfix z.val)
  have hzero : (κ z - 1) • x = 0 := by rw [sub_smul, one_smul, heq, sub_self]
  exact (smul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hz)

theorem finiteAverage_global_eq_zero_of_nontrivial_character [Finite G]
    (hC : _root_.commutator G ≤ Subgroup.center G) (ρ : G →* (H ≃ₗᵢ[ℂ] H))
    (κ : _root_.commutator G →* ℂ) (hκ : κ ≠ 1) (x : H)
    (hx : ∀ z : _root_.commutator G, ρ z.val x = κ z • x) :
    finiteSubgroupAverage ρ ⊤ x = 0 := by
  apply eq_zero_of_character_and_global_invariant ρ κ hκ
    (finiteSubgroupAverage ρ ⊤ x)
    (finiteSubgroupAverage_preserves_central_character hC ρ κ ⊤ x hx)
  intro g
  exact finiteSubgroupAverage_invariant ρ ⊤ x ⟨g, Subgroup.mem_top g⟩

variable [Finite G] [CompleteSpace H]

theorem finiteAverage_trivial_character_product
    (hC : _root_.commutator G ≤ Subgroup.center G) (ρ : G →* (H ≃ₗᵢ[ℂ] H))
    (A B : Subgroup G) (hgen : A ⊔ B = ⊤) (x : H)
    (hx : ∀ z : _root_.commutator G, ρ z.val x = x) :
    finiteSubgroupAverage ρ B (finiteSubgroupAverage ρ A x) = finiteSubgroupAverage ρ ⊤ x := by
  have hchar : ∀ z : _root_.commutator G, ρ z.val (finiteSubgroupAverage ρ A x) = finiteSubgroupAverage ρ A x := by
    simpa only [MonoidHom.one_apply, one_smul] using
      finiteSubgroupAverage_preserves_central_character hC ρ 1 A x
        (by simpa only [MonoidHom.one_apply, one_smul] using hx)
  have hfix := finiteAverage_trivial_character_invariant hC ρ A B hgen
    (finiteSubgroupAverage ρ A x) hchar (finiteSubgroupAverage_invariant ρ A x)
  have htop : finiteSubgroupAverage ρ ⊤ (finiteSubgroupAverage ρ B (finiteSubgroupAverage ρ A x)) =
      finiteSubgroupAverage ρ B (finiteSubgroupAverage ρ A x) :=
    finiteSubgroupAverage_of_invariant ρ ⊤ _ (fun g => hfix g.val)
  have hB := congrArg (fun T : H →L[ℂ] H => T (finiteSubgroupAverage ρ A x))
    (finiteSubgroupAverage_mul_of_ge ρ (show B ≤ ⊤ from le_top))
  have hA := congrArg (fun T : H →L[ℂ] H => T x)
    (finiteSubgroupAverage_mul_of_ge ρ (show A ≤ ⊤ from le_top))
  exact htop.symm.trans (hB.trans hA)

theorem finiteSubgroupAverage_apply_norm_le (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (A : Subgroup G) (x : H) :
    ‖finiteSubgroupAverage ρ A x‖ ≤ ‖x‖ := by
  rw [finiteSubgroupAverage_eq_projection]
  exact Submodule.norm_starProjection_apply_le _ x

end ThomGame.Analysis
