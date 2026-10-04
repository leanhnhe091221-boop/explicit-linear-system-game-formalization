module

public import ThomGame.Pictures.VertexErasureEuler
public import ThomGame.Pictures.ReturnTransport
public import ThomGame.Pictures.TwoStepReturn
public import ThomGame.Pictures.MarkedSurgery
public import ThomGame.Pictures.InvariantEuler

/-!
# First-return rotation on a retained edge set preserves saturation

Split an omitted slot out of its vertex orbit, leaving it as a singleton.
This does not change first returns to the retained slots. Iterating these
splits gives the first-return rotation on retained slots and fixes every
other slot. If the retained set is edge-invariant, its actual restriction
therefore satisfies Euler saturation. Entire omitted rotation orbits are
allowed; no boundary-accessibility premise is needed.
-/

@[expose] public section
namespace ThomGame.Pictures

open Equiv CycleSurgery RibbonConnectivity
open scoped Classical

namespace MarkedReturn

variable {D : Type*} [Finite D] [DecidableEq D] (r : Perm D) (M : D → Prop)

theorem perm_split_unmarked (a : D) (ha : ¬ M a) :
    perm (splice r a (r a)) M = perm r M := by
  by_cases hfix : r a = a
  · rw [hfix, splice, swap_self]
    rfl
  let N : D → Prop := fun x => x ≠ a
  have hMN : ∀ x, M x → N x := fun x hx he => ha (he ▸ hx)
  have hstep (x : Subtype N) :
      splice r a (r a) x.val = (perm r N x).val := by
    rw [splice_apply]
    by_cases hx : r x.val = a
    · rw [hx, swap_apply_left, perm_val_of_two_steps]
      · rw [hx]
      · exact fun h => h hx
      · change r (r x.val) ≠ a
        rwa [hx]
    · rw [swap_apply_of_ne_of_ne hx (fun he => x.property (r.injective he))]
      exact (perm_val_of_step r N x hx).symm
  ext x
  let xN : {y : Subtype N // M y.val} := ⟨⟨x.val, hMN x.val x.property⟩, x.property⟩
  have he := perm_preserved_of_commutes (splice r a (r a)) M (perm r N)
    (fun x : Subtype N => M x.val) Subtype.val hstep (fun _ => Iff.rfl) xN
  have hn := congrArg Subtype.val (perm_nested_subset r N M hMN xN)
  exact he.symm.trans hn.symm

end MarkedReturn

namespace RotationEuler

variable {D : Type*} [Finite D] [DecidableEq D] (r : Perm D) (M : D → Prop)

noncomputable def eraseSlots : Perm D :=
  Perm.extendDomain (MarkedReturn.perm r M) (Equiv.refl (Subtype M))

omit [DecidableEq D] in
theorem eraseSlots_kept (x : Subtype M) :
    eraseSlots r M x.val = (MarkedReturn.perm r M x).val :=
  Perm.extendDomain_apply_image _ (Equiv.refl (Subtype M)) x

omit [DecidableEq D] in
theorem eraseSlots_omitted (x : D) (hx : ¬ M x) : eraseSlots r M x = x :=
  Perm.extendDomain_apply_not_subtype _ _ hx

omit [DecidableEq D] in
theorem eraseSlots_preserves (x : D) : M (eraseSlots r M x) ↔ M x :=
  MarkedReturn.marked_iff_of_fixes_complement M (eraseSlots r M) (eraseSlots_omitted r M) x

omit [DecidableEq D] in
theorem eraseSlots_eq_of_fixed (hfix : ∀ x, ¬ M x → r x = x) : eraseSlots r M = r := by
  ext x
  by_cases hx : M x
  · have hn := (MarkedReturn.marked_iff_of_fixes_complement M r hfix x).mpr hx
    exact (eraseSlots_kept r M ⟨x, hx⟩).trans (MarkedReturn.perm_val_of_step r M ⟨x, hx⟩ hn)
  · exact (eraseSlots_omitted r M x hx).trans (hfix x hx).symm

theorem eraseSlots_split_unmarked (a : D) (ha : ¬ M a) :
    eraseSlots (splice r a (r a)) M = eraseSlots r M := by
  unfold eraseSlots
  rw [MarkedReturn.perm_split_unmarked r M a ha]

variable (t : Perm D)

theorem eraseSlots_saturated (ht : Function.Involutive t)
    (hEuler : count r t = 2 * Nat.card (Component r t)) :
    count (eraseSlots r M) t = 2 * Nat.card (Component (eraseSlots r M) t) := by
  let : Fintype D := Fintype.ofFinite D
  induction hn : r.support.card using Nat.strong_induction_on generalizing r with
  | h n ih =>
    by_cases hall : ∀ x, ¬ M x → r x = x
    · simpa only [eraseSlots_eq_of_fixed r M hall] using hEuler
    · obtain ⟨a, ha, hmove⟩ : ∃ a, ¬ M a ∧ r a ≠ a := by
        push Not at hall
        exact hall
      let r₀ := splice r a (r a)
      have hlt : r₀.support.card < n := by
        rw [← hn]
        exact Perm.card_support_swap_mul hmove
      have hs := ih r₀.support.card hlt r₀
        (splitVertex_saturated r t ht hEuler
          (show r.SameCycle a (r a) from Perm.SameCycle.rfl.apply_right)) rfl
      simpa only [r₀, eraseSlots_split_unmarked r M a ha] using hs

omit [DecidableEq D] in
theorem eraseSlots_subtype :
    (eraseSlots r M).subtypePerm (eraseSlots_preserves r M) = MarkedReturn.perm r M := by
  ext x
  exact eraseSlots_kept r M x

theorem firstReturnRotation_saturated (hM : ∀ x, M (t x) ↔ M x) (ht : Function.Involutive t)
    (hEuler : count r t = 2 * Nat.card (Component r t)) :
    count (MarkedReturn.perm r M) (t.subtypePerm hM) =
      2 * Nat.card (Component (MarkedReturn.perm r M) (t.subtypePerm hM)) := by
  have h := subtype_saturated (eraseSlots r M) t M (eraseSlots_preserves r M) hM ht
    (eraseSlots_saturated r M t ht hEuler)
  rwa [eraseSlots_subtype] at h

end RotationEuler
end ThomGame.Pictures
