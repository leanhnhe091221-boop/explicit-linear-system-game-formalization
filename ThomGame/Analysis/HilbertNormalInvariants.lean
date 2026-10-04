module

public import ThomGame.Analysis.HilbertUnitaryInvariants
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-! A normal subgroup's invariant Hilbert space carries the actual quotient representation. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def hilbertUnitaryRestriction (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (S : Submodule ℂ H)
    (hS : ∀ g : G, ∀ x ∈ S, ρ g x ∈ S) : G →* (S ≃ₗᵢ[ℂ] S) where
  toFun g := {
    toFun x := ⟨ρ g x.val, hS g x.val x.property⟩
    invFun x := ⟨ρ g⁻¹ x.val, hS g⁻¹ x.val x.property⟩
    map_add' x y := Subtype.ext ((ρ g).map_add x.val y.val)
    map_smul' c x := Subtype.ext ((ρ g).map_smul c x.val)
    left_inv x := Subtype.ext (by
      change ρ g⁻¹ (ρ g x.val) = x.val
      rw [← hilbertUnitary_apply_mul, inv_mul_cancel, map_one]
      rfl)
    right_inv x := Subtype.ext (by
      change ρ g (ρ g⁻¹ x.val) = x.val
      rw [← hilbertUnitary_apply_mul, mul_inv_cancel, map_one]
      rfl)
    norm_map' x := (ρ g).norm_map x.val }
  map_one' := by
    ext x
    exact congrArg (fun f : H ≃ₗᵢ[ℂ] H => f x.val) (map_one ρ)
  map_mul' g k := by
    ext x
    exact hilbertUnitary_apply_mul ρ g k x.val

theorem hilbertUnitaryRestriction_apply (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (S : Submodule ℂ H)
    (hS : ∀ g : G, ∀ x ∈ S, ρ g x ∈ S) (g : G) (x : S) :
    (hilbertUnitaryRestriction ρ S hS g x).val = ρ g x.val := rfl

theorem normalInvariants_stable (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (N : Subgroup G) [N.Normal]
    (g : G) (x : H) (hx : x ∈ hilbertUnitaryInvariants (ρ.comp N.subtype)) :
    ρ g x ∈ hilbertUnitaryInvariants (ρ.comp N.subtype) := by
  intro n
  have hconj : g⁻¹ * n.val * g ∈ N := Subgroup.Normal.conj_mem' inferInstance n.val n.property g
  have hfix := hx ⟨g⁻¹ * n.val * g, hconj⟩
  change ρ (g⁻¹ * n.val * g) x = x at hfix
  change ρ n.val (ρ g x) = ρ g x
  calc
    ρ n.val (ρ g x) = ρ g (ρ (g⁻¹ * n.val * g) x) := by
      simp only [← hilbertUnitary_apply_mul, mul_assoc, mul_inv_cancel_left]
    _ = ρ g x := by rw [hfix]

def normalInvariantsRepresentation (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (N : Subgroup G) [N.Normal] :
    G →* (hilbertUnitaryInvariants (ρ.comp N.subtype) ≃ₗᵢ[ℂ] hilbertUnitaryInvariants (ρ.comp N.subtype)) :=
  hilbertUnitaryRestriction ρ _ (normalInvariants_stable ρ N)

theorem normalInvariantsRepresentation_apply (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (N : Subgroup G) [N.Normal]
    (g : G) (x : hilbertUnitaryInvariants (ρ.comp N.subtype)) :
    (normalInvariantsRepresentation ρ N g x).val = ρ g x.val := rfl

theorem normalInvariantsRepresentation_kernel (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (N : Subgroup G) [N.Normal] :
    N ≤ (normalInvariantsRepresentation ρ N).ker := by
  intro n hn
  change normalInvariantsRepresentation ρ N n = 1
  ext x
  exact x.property ⟨n, hn⟩

def normalQuotientRepresentation (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (N : Subgroup G) [N.Normal] :
    G ⧸ N →* (hilbertUnitaryInvariants (ρ.comp N.subtype) ≃ₗᵢ[ℂ] hilbertUnitaryInvariants (ρ.comp N.subtype)) :=
  QuotientGroup.lift N (normalInvariantsRepresentation ρ N) (normalInvariantsRepresentation_kernel ρ N)

theorem normalQuotientRepresentation_mk (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (N : Subgroup G) [N.Normal]
    (g : G) (x : hilbertUnitaryInvariants (ρ.comp N.subtype)) :
    (normalQuotientRepresentation ρ N ((QuotientGroup.mk' N) g) x).val = ρ g x.val := rfl

theorem normalQuotientRepresentation_invariant_iff (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (N : Subgroup G) [N.Normal]
    (x : hilbertUnitaryInvariants (ρ.comp N.subtype)) :
    x ∈ hilbertUnitaryInvariants (normalQuotientRepresentation ρ N) ↔ x.val ∈ hilbertUnitaryInvariants ρ := by
  constructor
  · intro hx g
    exact congrArg Subtype.val (hx ((QuotientGroup.mk' N) g))
  · intro hx q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
    exact Subtype.ext (hx g)

end ThomGame.Analysis
