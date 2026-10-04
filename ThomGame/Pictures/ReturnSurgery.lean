module

public import ThomGame.Pictures.SpliceReturn

/-!
# Target exchanges commute with first return when their endpoints survive

A seam still present in the retained boundary can be exchanged either
before or after computing the current first-return permutation. The
proof expands the actual marked paths, so the equality concerns exact
successors rather than only orbit partitions.
-/

@[expose] public section
namespace ThomGame.Pictures.MarkedReturn

open Equiv CycleSurgery

variable {A : Type*} [DecidableEq A] [Finite A] (f : Perm A) (p : A → Prop)

omit [Finite A] in
theorem swap_subtype_val (a b x : Subtype p) :
    (swap a b x).val = swap a.val b.val x.val := by
  by_cases hxa : x = a
  · subst x
    simp only [swap_apply_left]
  by_cases hxb : x = b
  · subst x
    simp only [swap_apply_right]
  rw [swap_apply_of_ne_of_ne hxa hxb,
    swap_apply_of_ne_of_ne (fun he => hxa (Subtype.ext he)) (fun he => hxb (Subtype.ext he))]

/-- Restricting and then swapping two retained targets equals swapping
them in the original permutation and then restricting. -/
theorem perm_splice_retained (a b : Subtype p) :
    perm (splice f a.val b.val) p = splice (perm f p) a b := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  have hs : ∀ z, ¬ p z → swap a.val b.val z = z := by
    intro z hz
    exact swap_apply_of_ne_of_ne (fun he => hz (he.symm ▸ a.property))
      (fun he => hz (he.symm ▸ b.property))
  have hp := (hit_perm f p x).twist_targets (swap a.val b.val) hs
  have hv : (splice (perm f p) a b x).val = swap a.val b.val (perm f p x).val :=
    swap_subtype_val p a b (perm f p x)
  have hm : p (swap a.val b.val (perm f p x).val) := hv ▸ (splice (perm f p) a b x).property
  have he := eq_perm_of_hit (splice f a.val b.val) p x hm hp
  exact he.symm.trans hv.symm

end ThomGame.Pictures.MarkedReturn
