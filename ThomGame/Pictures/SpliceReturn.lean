module

public import ThomGame.Pictures.CircularPartition

/-!
# First returns after cutting at a consecutive pair in one orbit

If `f a = b`, exchanging the incoming targets `a,b` isolates `a`.
On any marked subset omitting these two points the genuine first return
is unchanged. In particular this settles the same-orbit case of deleting
two adjacent points of an ordered noncrossing permutation.
-/

@[expose] public section
namespace ThomGame.Pictures

open Equiv MarkedReturn

namespace CycleSurgery

variable {A : Type*} [DecidableEq A] [Finite A]

/-- The complete orbit relation after joining two different cycles. -/
theorem sameCycle_join_iff (f : Perm A) {a b : A} (hab : ¬ f.SameCycle a b)
    (x y : A) :
    (splice f a b).SameCycle x y ↔ f.SameCycle x y ∨
      (f.SameCycle x a ∧ f.SameCycle y b) ∨
      (f.SameCycle x b ∧ f.SameCycle y a) := by
  constructor
  · intro hxy
    have he := invariant_sameCycle (splice f a b) _ (mergedClass_splice f a b) hxy
    unfold mergedClass at he
    split_ifs at he with hx hy hy
    · exact Or.inl (((FiniteReturn.orbit_eq_iff f x b).mp hx).trans
        ((FiniteReturn.orbit_eq_iff f y b).mp hy).symm)
    · exact Or.inr (Or.inr ⟨(FiniteReturn.orbit_eq_iff f x b).mp hx,
        ((FiniteReturn.orbit_eq_iff f a y).mp he).symm⟩)
    · exact Or.inr (Or.inl ⟨(FiniteReturn.orbit_eq_iff f x a).mp he,
        (FiniteReturn.orbit_eq_iff f y b).mp hy⟩)
    · exact Or.inl ((FiniteReturn.orbit_eq_iff f x y).mp he)
  · rintro (hxy | ⟨hxa, hyb⟩ | ⟨hxb, hya⟩)
    · exact oldCycle_in_join f hab hxy
    · exact (oldCycle_in_join f hab hxa).trans
        ((joins f hab).trans (oldCycle_in_join f hab hyb).symm)
    · exact (oldCycle_in_join f hab hxb).trans
        ((joins f hab).symm.trans (oldCycle_in_join f hab hya).symm)

omit [Finite A] in
theorem splice_fixed_of_apply (f : Perm A) {a b : A} (hab : f a = b) :
    splice f a b a = a := by
  rw [splice_apply, hab, swap_apply_right]

omit [Finite A] in
/-- Every step away from the isolated point is one or two old steps. -/
theorem splice_hit_of_apply (f : Perm A) {a b : A} (hab : f a = b)
    (p : A → Prop) (ha : ¬ p a) {x : A} (hx : x ≠ a) :
    Hit f p x (splice f a b x) := by
  by_cases hxa : f x = a
  · rw [splice_apply, hxa, swap_apply_left]
    have hr : Hit f p a b := hab ▸ Hit.direct a
    exact Hit.skip x (hxa ▸ ha) (hxa.symm ▸ hr)
  · have hxb : f x ≠ b := fun he => hx (f.injective (he.trans hab.symm))
    rw [splice_apply, swap_apply_of_ne_of_ne hxa hxb]
    exact Hit.direct _

omit [Finite A] in
theorem expand_splice_hit_of_apply (f : Perm A) {a b : A} (hab : f a = b)
    (p : A → Prop) (ha : ¬ p a) {x y : A}
    (h : Hit (splice f a b) p x y) (hx : x ≠ a) : Hit f p x y := by
  induction h with
  | direct x => exact splice_hit_of_apply f hab p ha hx
  | skip x hn tail ih =>
    have hnext : splice f a b x ≠ a := by
      intro he
      exact hx ((splice f a b).injective (he.trans (splice_fixed_of_apply f hab).symm))
    exact (splice_hit_of_apply f hab p ha hx).append hn (ih hnext)

/-- Isolating an unmarked point does not change any marked successor. -/
theorem perm_splice_of_apply (f : Perm A) {a b : A} (hab : f a = b)
    (p : A → Prop) (ha : ¬ p a) : perm (splice f a b) p = perm f p := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  exact eq_perm_of_hit f p x (perm (splice f a b) p x).property
    (expand_splice_hit_of_apply f hab p ha (hit_perm (splice f a b) p x)
      (fun he => ha (he ▸ x.property)))

/-- Make one point a singleton, reconnecting its former predecessor to
its former successor. -/
def isolate (f : Perm A) (a : A) : Perm A := splice f a (f a)

omit [Finite A] in
theorem isolate_fixed (f : Perm A) (a : A) : isolate f a a = a :=
  splice_fixed_of_apply f rfl

theorem perm_isolate (f : Perm A) (a : A) (p : A → Prop) (ha : ¬ p a) :
    perm (isolate f a) p = perm f p := perm_splice_of_apply f rfl p ha

theorem sameCycle_isolate_away_iff (f : Perm A) (a : A) {x y : A}
    (hx : x ≠ a) (hy : y ≠ a) : (isolate f a).SameCycle x y ↔ f.SameCycle x y := by
  let p := fun x => x ≠ a
  have he := perm_isolate f a p (by simp [p])
  have hi := sameCycle_iff (isolate f a) p ⟨x, hx⟩ ⟨y, hy⟩
  rw [he] at hi
  exact hi.symm.trans (sameCycle_iff f p ⟨x, hx⟩ ⟨y, hy⟩)

end CycleSurgery

namespace CircularPartition

variable {A : Type*} [DecidableEq A] [Finite A]

omit [DecidableEq A] [Finite A] in
theorem Follows.apply_of_adjacent {c f : Perm A} (h : Follows c f)
    {a b : A} (hc : c a = b) (hf : f.SameCycle a b) : f a = b := by
  have hd : Hit c (f.SameCycle a) a b := hc ▸ Hit.direct a
  exact (h.at_self a).unique hd Perm.SameCycle.rfl.apply_right hf

/-- The same-orbit case of adjacent interface deletion, with no
assumption about an embedding in a geometric disk. -/
theorem OrderedNoncrossing.splice_restrict_sameCycle
    {c f : Perm A} {o : A → A → A → Prop} (h : OrderedNoncrossing c o f)
    {a b : A} (hc : c a = b) (hf : f.SameCycle a b)
    (p : A → Prop) (ha : ¬ p a) :
    OrderedNoncrossing (perm c p) (fun x y z : Subtype p => o x.val y.val z.val)
      (perm (CycleSurgery.splice f a b) p) := by
  rw [CycleSurgery.perm_splice_of_apply f (h.follows.apply_of_adjacent hc hf) p ha]
  exact h.restrict p

end CircularPartition
end ThomGame.Pictures
