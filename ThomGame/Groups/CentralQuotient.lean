module

public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Quotient by a specified central involution

The subgroup being killed is explicitly {1,j}. This gives the precise
kernel computation used in the last step of the wagon-wheel embedding.
The distinguished involution is allowed to equal the identity.
-/

@[expose] public section
namespace ThomGame.CentralQuotient

variable (G : Type*) [Group G]

structure Datum where
  j : G
  square : j * j = 1
  central : ∀ g, Commute j g

namespace Datum

variable {G} (D : Datum G)

def subgroup : Subgroup G where
  carrier := {g | g = 1 ∨ g = D.j}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro a b ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      simp [D.square]
  inv_mem' := by
    intro a ha
    rcases ha with rfl | rfl
    · simp
    · exact Or.inr (inv_eq_of_mul_eq_one_left D.square)

theorem mem_subgroup (g : G) : g ∈ D.subgroup ↔ g = 1 ∨ g = D.j := Iff.rfl

instance subgroup_normal : D.subgroup.Normal where
  conj_mem a ha g := by
    rcases ha with rfl | rfl
    · exact Or.inl (by simp)
    · apply Or.inr
      rw [← (D.central g).eq]
      simp [mul_assoc]

abbrev GroupOf := G ⧸ D.subgroup

def projection : G →* D.GroupOf := QuotientGroup.mk' D.subgroup

theorem projection_eq_one_iff (g : G) : D.projection g = 1 ↔ g = 1 ∨ g = D.j :=
  QuotientGroup.eq_one_iff g

theorem projection_j : D.projection D.j = 1 := (D.projection_eq_one_iff D.j).mpr (Or.inr rfl)

theorem projection_surjective : Function.Surjective D.projection := QuotientGroup.mk'_surjective _

variable {H : Type*} [Group H]

def lift (φ : G →* H) (hφ : φ D.j = 1) : D.GroupOf →* H :=
  QuotientGroup.lift D.subgroup φ (by
    intro g hg
    rcases hg with rfl | rfl
    · exact map_one φ
    · exact hφ)

theorem lift_projection (φ : G →* H) (hφ : φ D.j = 1) (g : G) :
    D.lift φ hφ (D.projection g) = φ g := rfl

theorem hom_ext {φ ψ : D.GroupOf →* H}
    (h : φ.comp D.projection = ψ.comp D.projection) : φ = ψ := by
  apply MonoidHom.ext
  intro q
  obtain ⟨g, rfl⟩ := D.projection_surjective q
  exact DFunLike.congr_fun h g

def map (E : Datum H) (φ : G →* H) (hφ : φ D.j = E.j) : D.GroupOf →* E.GroupOf :=
  D.lift (E.projection.comp φ) (by rw [MonoidHom.comp_apply, hφ, E.projection_j])

theorem map_projection (E : Datum H) (φ : G →* H) (hφ : φ D.j = E.j) (g : G) :
    D.map E φ hφ (D.projection g) = E.projection (φ g) := rfl

theorem injective_of_quotient_injective (E : Datum H) (φ : G →* H) (hφ : φ D.j = E.j)
    (hq : Function.Injective (D.map E φ hφ)) (hj : φ D.j = 1 → D.j = 1) :
    Function.Injective φ := by
  intro a b hab
  have hm : φ (a * b⁻¹) = 1 := by simp [hab]
  have hp : D.projection (a * b⁻¹) = 1 := by
    apply hq
    rw [map_projection, hm, map_one, map_one]
  rcases (D.projection_eq_one_iff _).mp hp with h | h
  · exact mul_inv_eq_one.mp h
  · have hJ : D.j = 1 := hj (by rw [← h]; exact hm)
    exact mul_inv_eq_one.mp (h.trans hJ)

end Datum
end ThomGame.CentralQuotient
