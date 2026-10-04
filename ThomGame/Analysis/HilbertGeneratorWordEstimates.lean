module

public import ThomGame.Groups.FiniteGeneratorWordBounds
public import ThomGame.Analysis.HilbertUnitaryInvariants

/-! Displacement bounds for genuine unitary representations propagate along finite words. -/

@[expose] public section
namespace ThomGame.Analysis

variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem hilbertUnitary_mul_displacement_le (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (g h : G) (x : H) :
    ‖ρ (g * h) x - x‖ ≤ ‖ρ g x - x‖ + ‖ρ h x - x‖ := by
  rw [hilbertUnitary_apply_mul]
  calc
    ‖ρ g (ρ h x) - x‖ ≤ ‖ρ g (ρ h x) - ρ g x‖ + ‖ρ g x - x‖ := by
      simpa only [dist_eq_norm] using dist_triangle (ρ g (ρ h x)) (ρ g x) x
    _ = ‖ρ g x - x‖ + ‖ρ h x - x‖ := by rw [← map_sub, (ρ g).norm_map, add_comm]

theorem hilbertUnitary_inv_displacement (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (g : G) (x : H) :
    ‖ρ g⁻¹ x - x‖ = ‖ρ g x - x‖ := by
  have h := (ρ g).norm_map (ρ g⁻¹ x - x)
  rw [map_sub, ← hilbertUnitary_apply_mul, mul_inv_cancel, map_one] at h
  change ‖x - ρ g x‖ = ‖ρ g⁻¹ x - x‖ at h
  exact h.symm.trans (norm_sub_rev _ _)

theorem generatorWordBound_displacement {S : Set G} {g : G} {n : Nat} (hw : GeneratorWordBound S g n)
    (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (x : H) (ε : ℝ)
    (hmove : ∀ s ∈ S, ‖ρ s x - x‖ ≤ ε) : ‖ρ g x - x‖ ≤ (n : ℝ) * ε := by
  induction hw with
  | one => simp only [map_one, LinearIsometryEquiv.coe_one, id_eq, sub_self, norm_zero, Nat.cast_zero, zero_mul, le_refl]
  | generator g hg => simpa only [Nat.cast_one, one_mul] using hmove g hg
  | @mul g h n m hwg hwh ihg ihh =>
      calc
        ‖ρ (g * h) x - x‖ ≤ ‖ρ g x - x‖ + ‖ρ h x - x‖ := hilbertUnitary_mul_displacement_le ρ g h x
        _ ≤ (n : ℝ) * ε + (m : ℝ) * ε := add_le_add ihg ihh
        _ = ((n + m : Nat) : ℝ) * ε := by rw [Nat.cast_add, add_mul]
  | @inv g n hw ih => rw [hilbertUnitary_inv_displacement]; exact ih

theorem finiteSetWordConstant_displacement (S : Set G) (K : Finset G)
    (hK : ∀ g ∈ K, g ∈ Subgroup.closure S) (ρ : G →* (H ≃ₗᵢ[ℂ] H))
    (x : H) (ε : ℝ) (hε : 0 ≤ ε) (hmove : ∀ s ∈ S, ‖ρ s x - x‖ ≤ ε)
    (g : G) (hg : g ∈ K) : ‖ρ g x - x‖ ≤ (finiteSetWordConstant S K hK : ℝ) * ε := by
  obtain ⟨n, hn, hw⟩ := finiteSetWordConstant_spec S K hK g hg
  exact (generatorWordBound_displacement hw ρ x ε hmove).trans
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn) hε)

end ThomGame.Analysis
