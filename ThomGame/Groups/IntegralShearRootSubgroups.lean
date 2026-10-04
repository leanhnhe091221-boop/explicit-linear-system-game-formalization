module

public import ThomGame.Groups.IntegralShearMatrixModel
public import Mathlib.GroupTheory.Commutator.Basic

/-! The actual six integer root subgroups and their exact A2 commutator relations. -/

@[expose] public section
namespace ThomGame.IntegralShear

open Compressor
open scoped commutatorElement

def rootHom (r : Root) : Multiplicative ℤ →* ShearGroup where
  toFun m := rootElement r m.toAdd
  map_one' := rootElement_zero r
  map_mul' m n := rootElement_add r m.toAdd n.toAdd

def rootSubgroup (r : Root) : Subgroup ShearGroup := (rootHom r).range

def rootPairSubgroup (r : Root) : Subgroup ShearGroup := rootSubgroup r ⊔ rootSubgroup (right r)

theorem mem_rootSubgroup (r : Root) (g : ShearGroup) :
    g ∈ rootSubgroup r ↔ ∃ m : ℤ, rootElement r m = g := by
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m.toAdd, hm⟩
  · rintro ⟨m, hm⟩
    exact ⟨Multiplicative.ofAdd m, hm⟩

theorem rootElement_mem_rootSubgroup (r : Root) (m : ℤ) : rootElement r m ∈ rootSubgroup r :=
  (mem_rootSubgroup r _).mpr ⟨m, rfl⟩

theorem of_mem_rootSubgroup (r : Root) : of r ∈ rootSubgroup r :=
  (rootElement_one r) ▸ rootElement_mem_rootSubgroup r 1

theorem rootHom_injective (r : Root) : Function.Injective (rootHom r) := by
  intro m n h
  apply Multiplicative.toAdd.injective
  exact rootElement_injective r h

theorem rootSubgroup_abelian (r : Root) :
    ∀ g ∈ rootSubgroup r, ∀ h ∈ rootSubgroup r, Commute g h := by
  intro g hg h hh
  obtain ⟨m, rfl⟩ := (mem_rootSubgroup r g).mp hg
  obtain ⟨n, rfl⟩ := (mem_rootSubgroup r h).mp hh
  exact (Commute.refl (of r)).zpow_zpow m n

theorem rootSubgroup_commute (r s : Root) (hrs : separated r s) :
    ∀ g ∈ rootSubgroup r, ∀ h ∈ rootSubgroup s, Commute g h := by
  intro g hg h hh
  obtain ⟨m, rfl⟩ := (mem_rootSubgroup r g).mp hg
  obtain ⟨n, rfl⟩ := (mem_rootSubgroup s h).mp hh
  exact rootElement_commute r s hrs m n

theorem rootSubgroup_commutator (r : Root) :
    ⁅rootSubgroup r, rootSubgroup (right r)⁆ = rootSubgroup (across r) := by
  apply le_antisymm
  · apply Subgroup.commutator_le.mpr
    intro g hg h hh
    obtain ⟨m, rfl⟩ := (mem_rootSubgroup r g).mp hg
    obtain ⟨n, rfl⟩ := (mem_rootSubgroup (right r) h).mp hh
    rw [rootElement_commutator]
    exact rootElement_mem_rootSubgroup _ _
  · intro g hg
    obtain ⟨m, rfl⟩ := (mem_rootSubgroup (across r) g).mp hg
    have h := Subgroup.commutator_mem_commutator (rootElement_mem_rootSubgroup r m)
      (rootElement_mem_rootSubgroup (right r) 1)
    simpa only [rootElement_commutator, mul_one] using h

theorem rootSubgroups_generate : (⨆ r : Root, rootSubgroup r) = ⊤ := by
  apply top_unique
  rw [← rootElements_generate]
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨r, rfl⟩
  exact (le_iSup (fun s : Root => rootSubgroup s) r) (of_mem_rootSubgroup r)

theorem rootPair_contains_center (r : Root) : rootSubgroup (across r) ≤ rootPairSubgroup r := by
  rw [← rootSubgroup_commutator]
  exact Subgroup.commutator_le_sup _ _

theorem of_heisenberg_relation (r : Root) :
    of r * of (right r) = of (right r) * of (across r) * of r := by
  have hc := of_commute (across r) (right r) (by revert r; decide +kernel)
  have h := rootElement_conjugate r 1 1
  simp only [rootElement_one, one_mul] at h
  calc
    of r * of (right r) = (of r * of (right r) * (of r)⁻¹) * of r := by simp only [mul_assoc, inv_mul_cancel, mul_one]
    _ = (of (across r) * of (right r)) * of r := by rw [h]
    _ = of (right r) * of (across r) * of r := by rw [hc.eq]

end ThomGame.IntegralShear
