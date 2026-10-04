module

public import Mathlib.Data.Fintype.Sum
public import Mathlib.SetTheory.Cardinal.Finite

/-! # Counting a disjoint union of two subsets and one distinguished element -/

@[expose] public section
namespace ThomGame.Finite

open scoped Classical

theorem card_partition_two_singleton {A : Type*} [Finite A]
    (M L R : A → Prop) (e : A)
    (hcover : ∀ x, M x ↔ L x ∨ R x ∨ x = e)
    (hdisjoint : ∀ x, ¬ (L x ∧ R x)) (hL : ¬ L e) (hR : ¬ R e) :
    Nat.card {x // M x} = Nat.card {x // L x} + Nat.card {x // R x} + 1 := by
  have hLR : Disjoint L (fun x => R x ∨ x = e) := by
    intro p hp hq x hx
    rcases hq x hx with hr | he
    · exact hdisjoint x ⟨hp x hx, hr⟩
    · exact hL (he ▸ hp x hx)
  have hRe : Disjoint R (fun x => x = e) := by
    intro p hp hq x hx
    exact hR (hq x hx ▸ hp x hx)
  have h₀ := Nat.card_congr (Equiv.subtypeEquivRight hcover)
  have h₁ := Nat.card_congr (subtypeOrEquiv L (fun x => R x ∨ x = e) hLR)
  have h₂ := Nat.card_congr (subtypeOrEquiv R (fun x => x = e) hRe)
  rw [Nat.card_sum] at h₁ h₂
  have he : Nat.card {x : A // x = e} = 1 := by
    let : Fintype {x : A // x = e} := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_eq]
  rw [h₀, h₁, h₂, he]
  omega

end ThomGame.Finite
