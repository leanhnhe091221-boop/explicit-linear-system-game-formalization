module

public import ThomGame.Groups.CentralCommutatorPairing

/-! A nontrivial character of the derived group detects a cross-root commutator. -/

@[expose] public section
namespace ThomGame

open scoped commutatorElement

variable {G R : Type*} [Group G] [Monoid R]

theorem commutator_character_eq_one_of_cross (hC : _root_.commutator G ≤ Subgroup.center G)
    (A B : Subgroup G) (hgen : A ⊔ B = ⊤)
    (hA : ∀ a ∈ A, ∀ a' ∈ A, Commute a a') (hB : ∀ b ∈ B, ∀ b' ∈ B, Commute b b')
    (κ : _root_.commutator G →* R)
    (hcross : ∀ a : A, ∀ b : B, κ (commutatorElementIn a.val b.val) = 1) : κ = 1 := by
  let S : Set G := (A : Set G) ∪ (B : Set G)
  have hS : Subgroup.closure S = ⊤ := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq, hgen]
  have htriple : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, Commute ⁅x, y⁆ z := by
    intro x _ y _ z _
    exact (Subgroup.mem_center_iff.mp (hC (commutatorElementIn x y).property) z).symm
  have hκpair : ∀ x ∈ S, ∀ y ∈ S, commutatorElementIn x y ∈ κ.ker := by
    intro x hx y hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · have heq : commutatorElementIn x y = 1 := Subtype.ext (hA x hx y hy).commutator_eq
      rw [heq]
      exact κ.ker.one_mem
    · exact hcross ⟨x, hx⟩ ⟨y, hy⟩
    · have heq : commutatorElementIn x y = (commutatorElementIn y x)⁻¹ :=
        Subtype.ext (commutatorElement_inv y x).symm
      rw [heq]
      exact κ.ker.inv_mem (hcross ⟨y, hy⟩ ⟨x, hx⟩)
    · have heq : commutatorElementIn x y = 1 := Subtype.ext (hB x hx y hy).commutator_eq
      rw [heq]
      exact κ.ker.one_mem
  have hle : _root_.commutator G ≤ κ.ker.map (_root_.commutator G).subtype := by
    conv_lhs => rw [commutator_eq_generatorCommutatorSubgroup hS htriple]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨⟨x, y⟩, rfl⟩
    exact ⟨commutatorElementIn x.val y.val, hκpair x.val x.property y.val y.property, rfl⟩
  apply MonoidHom.ext
  intro z
  obtain ⟨w, hw, hwz⟩ := hle z.property
  have heq : w = z := Subtype.ext hwz
  subst w
  exact hw

theorem commutatorCharacterAnnihilator_ne_top (hC : _root_.commutator G ≤ Subgroup.center G)
    (A B : Subgroup G) (hgen : A ⊔ B = ⊤)
    (hA : ∀ a ∈ A, ∀ a' ∈ A, Commute a a') (hB : ∀ b ∈ B, ∀ b' ∈ B, Commute b b')
    (κ : _root_.commutator G →* R) (hκ : κ ≠ 1) :
    commutatorCharacterAnnihilator hC κ A B ≠ ⊤ := by
  intro htop
  apply hκ
  apply commutator_character_eq_one_of_cross hC A B hgen hA hB κ
  intro a b
  have hb : b ∈ commutatorCharacterAnnihilator hC κ A B := by rw [htop]; trivial
  exact (mem_commutatorCharacterAnnihilator hC κ A B b).mp hb a

end ThomGame
