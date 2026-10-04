module

public import ThomGame.Pictures.EdgeDeletionEuler

/-! # Restoring one deleted edge in an arbitrary retained-edge graph -/

@[expose] public section
namespace ThomGame.Pictures.RotationEuler

open Equiv CycleSurgery RibbonConnectivity
open scoped Classical

variable {D : Type*} (t : Perm D) (M : D → Prop) (hM : ∀ x, M (t x) ↔ M x)
  (a b : D) (hta : t a = b) (htb : t b = a) (hMa : M a)
  (q : Perm D) (hq : ∀ x, q x = if (x ≠ a ∧ x ≠ b) ∧ M x then t x else x)

include hta htb hMa hq in
theorem restore_deleted_pair : splice q a b = retainEdges t M hM := by
  have hMb : M b := hta ▸ (hM a).mpr hMa
  ext x
  rw [splice_apply, hq, retainEdges_apply]
  by_cases hxa : x = a
  · subst x
    simp [hMa, hta]
  by_cases hxb : x = b
  · subst x
    simp [hMb, htb]
  by_cases hx : M x
  · rw [ite_eq_left ⟨⟨hxa, hxb⟩, hx⟩, ite_eq_left hx]
    apply swap_apply_of_ne_of_ne
    · intro he
      exact hxb (t.injective (he.trans htb.symm))
    · intro he
      exact hxa (t.injective (he.trans hta.symm))
  · rw [ite_eq_right (fun h => hx h.2), ite_eq_right hx]
    exact swap_apply_of_ne_of_ne hxa hxb

include hta htb hMa hq in
theorem restored_connected_iff (f : Perm D) (x y : D) :
    Connected f (retainEdges t M hM) x y ↔ Connected f q x y ∨
      (Connected f q x a ∧ Connected f q y b) ∨
      (Connected f q x b ∧ Connected f q y a) := by
  rw [← restore_deleted_pair t M hM a b hta htb hMa q hq]
  have hqa : q a = a := by simp [hq]
  exact connected_splice_iff_of_seam f q (seam_of_fixed f q hqa) x y

include hta htb hMa hq in
theorem restored_connected_return_iff (f : Perm D) (x y : D) :
    Connected f (retainEdges t M hM) x y ↔ Connected f q x y ∨
      (Connected f q x (f a) ∧ Connected f q y (f b)) ∨
      (Connected f q x (f b) ∧ Connected f q y (f a)) := by
  have ha (z : D) : Connected f q z a ↔ Connected f q z (f a) :=
    ⟨fun h => h.trans (Connected.edge a), fun h => h.trans (Connected.edge a).symm⟩
  have hb (z : D) : Connected f q z b ↔ Connected f q z (f b) :=
    ⟨fun h => h.trans (Connected.edge b), fun h => h.trans (Connected.edge b).symm⟩
  rw [restored_connected_iff t M hM a b hta htb hMa q hq, ha, hb, hb, ha]

end ThomGame.Pictures.RotationEuler
