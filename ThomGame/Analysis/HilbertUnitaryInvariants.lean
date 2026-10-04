module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Algebra.Group.Subgroup.Lattice

/-! Actual invariant Hilbert subspaces of arbitrary unitary representations. -/

@[expose] public section
namespace ThomGame.Analysis

variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def hilbertUnitaryInvariants (ρ : G →* (H ≃ₗᵢ[ℂ] H)) : Submodule ℂ H where
  carrier := {x | ∀ g, ρ g x = x}
  zero_mem' := by intro g; exact map_zero (ρ g)
  add_mem' := by intro x y hx hy g; rw [map_add, hx, hy]
  smul_mem' := by intro c x hx g; rw [map_smul, hx]

theorem mem_hilbertUnitaryInvariants (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (x : H) :
    x ∈ hilbertUnitaryInvariants ρ ↔ ∀ g, ρ g x = x := Iff.rfl

theorem hilbertUnitaryInvariants_isClosed (ρ : G →* (H ≃ₗᵢ[ℂ] H)) :
    IsClosed (hilbertUnitaryInvariants ρ : Set H) := by
  change IsClosed {x : H | ∀ g, ρ g x = x}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter (fun g => isClosed_eq (ρ g).continuous continuous_id)

instance [CompleteSpace H] (ρ : G →* (H ≃ₗᵢ[ℂ] H)) : CompleteSpace (hilbertUnitaryInvariants ρ) :=
  (hilbertUnitaryInvariants_isClosed ρ).completeSpace_coe

theorem hilbertUnitary_apply_mul (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (g h : G) (x : H) :
    ρ (g * h) x = ρ g (ρ h x) := by rw [map_mul]; rfl

def hilbertVectorStabilizer (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (x : H) : Subgroup G where
  carrier := {g | ρ g x = x}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change ρ g x = x at hg
    change ρ h x = x at hh
    change ρ (g * h) x = x
    rw [hilbertUnitary_apply_mul, hh, hg]
  inv_mem' := by
    intro g hg
    change ρ g x = x at hg
    change ρ g⁻¹ x = x
    apply (ρ g).injective
    rw [← hilbertUnitary_apply_mul, mul_inv_cancel, map_one, hg]
    rfl

theorem hilbertUnitaryInvariants_of_iSup {ι : Type*} (ρ : G →* (H ≃ₗᵢ[ℂ] H))
    (K : ι → Subgroup G) (hgen : (⨆ i, K i) = ⊤) :
    hilbertUnitaryInvariants ρ = ⨅ i, hilbertUnitaryInvariants (ρ.comp (K i).subtype) := by
  ext x
  simp only [Submodule.mem_iInf]
  constructor
  · intro hx i g
    exact hx g.val
  · intro hx
    have hle : (⨆ i, K i) ≤ hilbertVectorStabilizer ρ x := by
      apply iSup_le
      intro i g hg
      exact hx i ⟨g, hg⟩
    rw [hgen] at hle
    intro g
    exact hle (Subgroup.mem_top g)

theorem hilbertUnitary_inner_fixed_left (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (x : H)
    (hx : x ∈ hilbertUnitaryInvariants ρ) (g : G) (y : H) :
    inner ℂ x (ρ g y) = inner ℂ x y := by
  conv_lhs => lhs; rw [← hx g]
  exact (ρ g).inner_map_map x y

/-- Generator fixed vectors are fixed by the subgroup they actually generate. -/
theorem hilbertUnitary_fixed_of_generators (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (S : Set G)
    (hgen : Subgroup.closure S = ⊤) (x : H) (hx : ∀ g ∈ S, ρ g x = x) :
    x ∈ hilbertUnitaryInvariants ρ := by
  intro g
  have hg : g ∈ Subgroup.closure S := by rw [hgen]; trivial
  induction hg using Subgroup.closure_induction with
  | mem g hg => exact hx g hg
  | one => simp
  | mul g h hg hh ihg ihh => rw [hilbertUnitary_apply_mul, ihh, ihg]
  | inv g hg ih =>
      apply (ρ g).injective
      rw [← hilbertUnitary_apply_mul, mul_inv_cancel, map_one, ih]
      rfl

end ThomGame.Analysis
