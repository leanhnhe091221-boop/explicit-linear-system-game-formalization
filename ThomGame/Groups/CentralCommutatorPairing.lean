module

public import ThomGame.Groups.CentralCommutatorExponent

/-! The actual commutator pairing and its scalar-character annihilator subgroup. -/

@[expose] public section
namespace ThomGame

open scoped commutatorElement

variable {G : Type*} [Group G]

def commutatorElementIn (a b : G) : _root_.commutator G :=
  ⟨⁅a, b⁆, Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)⟩

theorem centralCommutator_mul_right (hC : _root_.commutator G ≤ Subgroup.center G) (a b c : G) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  have hc : Commute b ⁅a, c⁆ := Subgroup.mem_center_iff.mp (hC (commutatorElementIn a c).property) b
  rw [commutatorElement_mul_right_eq_mul_conj]
  calc
    ⁅a, b⁆ * b * ⁅a, c⁆ * b⁻¹ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by simp only [mul_assoc]
    _ = _ := by rw [hc.eq, mul_inv_cancel_right]

def centralCommutatorRight (hC : _root_.commutator G ≤ Subgroup.center G) (a : G) :
    G →* _root_.commutator G where
  toFun b := commutatorElementIn a b
  map_one' := Subtype.ext (commutatorElement_one_right a)
  map_mul' b c := Subtype.ext (centralCommutator_mul_right hC a b c)

variable {R : Type*} [Monoid R]

def commutatorCharacterAnnihilator (hC : _root_.commutator G ≤ Subgroup.center G)
    (κ : _root_.commutator G →* R) (A B : Subgroup G) : Subgroup B :=
  ⨅ a : A, ((κ.comp (centralCommutatorRight hC a.val)).comp B.subtype).ker

theorem mem_commutatorCharacterAnnihilator (hC : _root_.commutator G ≤ Subgroup.center G)
    (κ : _root_.commutator G →* R) (A B : Subgroup G) (b : B) :
    b ∈ commutatorCharacterAnnihilator hC κ A B ↔ ∀ a : A, κ (commutatorElementIn a.val b.val) = 1 := by
  simp only [commutatorCharacterAnnihilator, Subgroup.mem_iInf, MonoidHom.mem_ker,
    MonoidHom.comp_apply, centralCommutatorRight]
  rfl

theorem commutatorCharacterAnnihilator_index {p : Nat} [Fact p.Prime]
    (hC : _root_.commutator G ≤ Subgroup.center G) (κ : _root_.commutator G →* R)
    (A B : Subgroup G) [Finite B] (hB : IsPGroup p B)
    (hproper : commutatorCharacterAnnihilator hC κ A B ≠ ⊤) :
    p ≤ (commutatorCharacterAnnihilator hC κ A B).index :=
  prime_le_index_of_proper hB _ hproper

end ThomGame
