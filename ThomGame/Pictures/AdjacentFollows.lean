module

public import ThomGame.Pictures.AdjacentNoninterlacing
public import ThomGame.Pictures.CircularReturnOrder

/-!
# Orientation after merging and deleting adjacent boundary points

First isolate the first seam point in the spliced permutation. This
retains exactly the first return on every subset omitting that point.
The remaining successor follows the original circle, as proved by
excluding orbit points from each intervening circular interval.
-/

@[expose] public section
namespace ThomGame.Pictures.CircularPartition

open Equiv MarkedReturn CycleSurgery

variable {n : Nat}

theorem not_between_adjacent (a z : Fin n) : ¬ sbtw a z (finRotate n a) := by
  let : NeZero n := a.neZero
  have hr := FinCircle.rotate_val a
  have hz := z.isLt
  simp only [Fin.sbtw_iff, Fin.lt_def]
  split_ifs at hr <;> omega

theorem adjacent_between (a : Fin n) {z : Fin n}
    (hza : z ≠ a) (hzb : z ≠ finRotate n a) : sbtw a (finRotate n a) z := by
  have ha : a ≠ finRotate n a := by
    intro he
    let : NeZero n := a.neZero
    have hr := FinCircle.rotate_val a
    have hv := congrArg Fin.val he
    have hz := z.isLt
    have hza' : z.val ≠ a.val := fun he => hza (Fin.ext he)
    split_ifs at hr <;> omega
  exact (strict_order_dichotomy ha hzb.symm hza).resolve_right (not_between_adjacent a z)

/-- Isolating the first seam point after joining puts the merged orbit
back into the correct ambient direction. -/
theorem OrderedNoncrossing.follows_isolate_splice
    {f : Perm (Fin n)}
    (h : OrderedNoncrossing (finRotate n) (sbtw : Fin n → Fin n → Fin n → Prop) f)
    (a : Fin n) (hab : ¬ f.SameCycle a (finRotate n a)) :
    Follows (finRotate n) (isolate (splice f a (finRotate n a)) a) := by
  let b := finRotate n a
  have hab' : a ≠ b := fun he => hab (he.sameCycle f)
  have hfab : f a ≠ b := fun he => hab
    ((show f.SameCycle a (f a) from Perm.SameCycle.rfl.apply_right).trans (he.sameCycle f))
  by_cases hfaa : f a = a
  · have he : isolate (splice f a b) a = f := by
      have hga : splice f a b a = b := by rw [splice_apply, hfaa, swap_apply_left]
      dsimp [isolate]
      rw [hga, splice_splice]
    change Follows (finRotate n) (isolate (splice f a b) a)
    rw [he]
    exact h.follows
  have hga : splice f a b a = f a := by
    rw [splice_apply, swap_apply_of_ne_of_ne hfaa hfab]
  have hstepA : ∀ x, f x = a → isolate (splice f a b) a x = b := by
    intro x hxa
    simp only [isolate, splice_apply, hga, hxa, swap_apply_left]
    exact swap_apply_of_ne_of_ne hab'.symm hfab.symm
  have hstepB : ∀ x, f x = b → isolate (splice f a b) a x = f a := by
    intro x hxb
    simp only [isolate, splice_apply, hga, hxb, swap_apply_right, swap_apply_left]
  have hstepOther : ∀ x, x ≠ a → f x ≠ a → f x ≠ b →
      isolate (splice f a b) a x = f x := by
    intro x hxa hfa hfb
    have hff : f x ≠ f a := fun he => hxa (f.injective he)
    simp only [isolate, splice_apply, hga, swap_apply_of_ne_of_ne hfa hfb,
      swap_apply_of_ne_of_ne hfa hff]
  apply follows_of_no_between
  intro x z hxz hbetween
  by_cases hxa : x = a
  · subst x
    rw [isolate_fixed] at hbetween
    exact sbtw_irrefl_left_right hbetween
  have hza : z ≠ a := by
    intro he
    subst z
    exact hxa (hxz.eq_of_right (isolate_fixed _ _))
  have hg := (sameCycle_isolate_away_iff (splice f a b) a hxa hza).mp hxz
  by_cases hfxa : f x = a
  · rw [hstepA x hfxa] at hbetween
    have hxfa : f.SameCycle x a := hfxa ▸ Perm.SameCycle.rfl.apply_right
    have hxb : x ≠ b := by
      intro he
      subst x
      exact hab hxfa.symm
    have hzb : z ≠ b := by
      intro he
      subst z
      exact sbtw_irrefl_right hbetween
    have hbetween' : sbtw x z a :=
      ((adjacent_arc_iff a hza hzb hxa hxb).mpr hbetween.cyclic_left).cyclic_right
    rcases (sameCycle_join_iff f hab x z).mp hg with hxz' | ⟨_, hzb'⟩ | ⟨hxb', _⟩
    · exact h.follows.no_between x z hxz' (hfxa ▸ hbetween')
    · have hbad := h.noninterlacing.arc_invariant hxfa
        (fun hxz' => hab (hxfa.symm.trans (hxz'.trans hzb'))) hzb' hbetween'
      exact not_between_adjacent a x hbad.cyclic_right
    · exact hab (hxfa.symm.trans hxb')
  by_cases hfxb : f x = b
  · rw [hstepB x hfxb] at hbetween
    have hxfb : f.SameCycle x b := hfxb ▸ Perm.SameCycle.rfl.apply_right
    have haf : f.SameCycle a (f a) := Perm.SameCycle.rfl.apply_right
    have haxf : sbtw a x (f a) := h.noninterlacing.arc_invariant haf hab hxfb.symm
      (adjacent_between a hfaa hfab)
    have contraA : f.SameCycle z a → False := by
      intro hza'
      exact h.follows.no_between a z hza'.symm (haxf.trans_left hbetween)
    have contraB : f.SameCycle x z → False := by
      intro hxz'
      by_cases hxb : x = b
      · have hfix : f x = x := hfxb.trans hxb.symm
        have he := hxz'.eq_of_left hfix
        subst z
        exact sbtw_irrefl_left hbetween
      · have hbxf : sbtw b x (f a) :=
          ((adjacent_arc_iff a hfaa hfab hxa hxb).mp haxf.cyclic_right).cyclic_left
        exact h.follows.no_between x z hxz' (hfxb ▸ hbetween.trans_right hbxf.cyclic_left)
    rcases (sameCycle_join_iff f hab x z).mp hg with hxz' | ⟨hxa', _⟩ | ⟨_, hza'⟩
    · exact contraB hxz'
    · exact hab (hxa'.symm.trans hxfb)
    · exact contraA hza'
  rw [hstepOther x hxa hfxa hfxb] at hbetween
  rcases (sameCycle_join_iff f hab x z).mp hg with hxz' | ⟨hxa', hzb'⟩ | ⟨hxb', hza'⟩
  · exact h.follows.no_between x z hxz' hbetween
  · have hxb : x ≠ b := fun he => hab (hxa'.symm.trans (he.sameCycle f))
    have hsep : sbtw x b (f x) := h.noninterlacing.arc_invariant
      Perm.SameCycle.rfl.apply_right
      (fun hxz' => hab (hxa'.symm.trans (hxz'.trans hzb'))) hzb' hbetween
    exact h.follows.no_between x a hxa'
      ((adjacent_arc_iff a hxa hxb hfxa hfxb).mpr hsep)
  · have hsep : sbtw x a (f x) := h.noninterlacing.arc_invariant
      Perm.SameCycle.rfl.apply_right
      (fun hxz' => hab ((hxz'.trans hza').symm.trans hxb')) hza' hbetween
    by_cases hxb : x = b
    · rw [hxb] at hsep
      exact not_between_adjacent a (f b) hsep.cyclic_left
    · exact h.follows.no_between x b hxb'
        ((adjacent_arc_iff a hxa hxb hfxa hfxb).mp hsep)

/-- Exchange adjacent targets and then take the genuine first return to
any subset omitting both. Both orbit separation and direction survive.
No same-cycle condition on the seam pair is needed. -/
theorem OrderedNoncrossing.splice_restrict_adjacent
    {f : Perm (Fin n)}
    (h : OrderedNoncrossing (finRotate n) (sbtw : Fin n → Fin n → Fin n → Prop) f)
    (a : Fin n) (p : Fin n → Prop) (ha : ¬ p a) (hb : ¬ p (finRotate n a)) :
    OrderedNoncrossing (perm (finRotate n) p)
      (fun x y z : Subtype p => sbtw x.val y.val z.val)
      (perm (splice f a (finRotate n a)) p) := by
  by_cases hab : f.SameCycle a (finRotate n a)
  · exact h.splice_restrict_sameCycle rfl hab p ha
  · refine ⟨?_, ?_⟩
    · have hf := (h.follows_isolate_splice a hab).restrict p
      rw [perm_isolate _ a p ha] at hf
      exact hf
    · apply h.noninterlacing.splice_restrict_of_arc_iff hab p
      intro x y
      exact adjacent_arc_iff a (fun he => ha (he ▸ x.property))
        (fun he => hb (he ▸ x.property)) (fun he => ha (he ▸ y.property))
        (fun he => hb (he ▸ y.property))

end ThomGame.Pictures.CircularPartition
