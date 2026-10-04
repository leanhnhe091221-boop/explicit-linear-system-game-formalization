module

public import ThomGame.Pictures.ComponentSurgery

/-!
# Component counts when joining two previously fixed edge ports

The splice lemmas extend whenever the exchanged endpoints are connected
after the exchange. In particular, if one endpoint was fixed by the
permutation being changed, its new edge connects the two endpoints.
This supports adding the transpositions of an edge involution one by one.
-/

@[expose] public section
namespace ThomGame.Pictures.RibbonConnectivity

open Equiv CycleSurgery
open scoped Classical

variable {D : Type*} [DecidableEq D] (p f : Perm D) {a b : D}

theorem old_connected_of_seam (hs : Connected p (splice f a b) a b)
    {x y : D} (hxy : Connected p f x y) : Connected p (splice f a b) x y := by
  apply hxy.lift id ⟨Connected.refl, Connected.symm, Connected.trans⟩
  · exact Connected.edge
  · intro x
    change Connected p (splice f a b) x (f x)
    have hx : Connected p (splice f a b) x (splice f a b x) := Connected.circuit _
    by_cases hxa : f x = a
    · rw [splice_apply, hxa, swap_apply_left] at hx
      rw [hxa]
      exact hx.trans hs.symm
    by_cases hxb : f x = b
    · rw [splice_apply, hxb, swap_apply_right] at hx
      rw [hxb]
      exact hx.trans hs
    · rw [splice_apply, swap_apply_of_ne_of_ne hxa hxb] at hx
      exact hx

theorem connected_splice_iff_of_seam (hs : Connected p (splice f a b) a b) (x y : D) :
    Connected p (splice f a b) x y ↔ Connected p f x y ∨
      (Connected p f x a ∧ Connected p f y b) ∨
      (Connected p f x b ∧ Connected p f y a) := by
  constructor
  · intro hxy
    exact rel_of_mergedClass_eq p f
      (hxy.invariant (mergedClass p f a b) (mergedClass_edge p f a b) (mergedClass_splice p f a b))
  · rintro (hxy | ⟨hxa, hyb⟩ | ⟨hxb, hya⟩)
    · exact old_connected_of_seam p f hs hxy
    · exact (old_connected_of_seam p f hs hxa).trans
        (hs.trans (old_connected_of_seam p f hs hyb).symm)
    · exact (old_connected_of_seam p f hs hxb).trans
        (hs.symm.trans (old_connected_of_seam p f hs hya).symm)

theorem mergeComponent_injective_of_seam (hs : Connected p (splice f a b) a b) :
    Function.Injective (mergeComponent p f a b) := by
  intro c d hcd
  refine Quotient.inductionOn₂ c d (fun x y he => ?_) hcd
  apply (component_eq_iff p (splice f a b) x y).mpr
  exact (connected_splice_iff_of_seam p f hs x y).mpr (rel_of_mergedClass_eq p f he)

noncomputable def joinedComponentEquiv_of_seam (hs : Connected p (splice f a b) a b)
    (hab : ¬ Connected p f a b) :
    Component p (splice f a b) ≃ {c : Component p f // c ≠ component p f b} :=
  Equiv.ofBijective
    (fun c => ⟨mergeComponent p f a b c, mergeComponent_ne p f hab c⟩)
    ⟨fun _ _ h => mergeComponent_injective_of_seam p f hs (congrArg Subtype.val h), by
      rintro ⟨c, hc⟩
      refine Quotient.inductionOn c (fun x hx => ?_) hc
      change component p f x ≠ component p f b at hx
      refine ⟨component p (splice f a b) x, Subtype.ext ?_⟩
      change mergedClass p f a b x = component p f x
      simp only [mergedClass, ite_eq_right hx]⟩

theorem seam_of_fixed (ha : f a = a) : Connected p (splice f a b) a b := by
  have h : splice f a b a = b := by rw [splice_apply, ha, swap_apply_left]
  have hc : Connected p (splice f a b) a (splice f a b a) := Connected.circuit a
  rwa [h] at hc

theorem component_card_same_of_fixed (ha : f a = a) (hab : Connected p f a b) :
    Nat.card (Component p (splice f a b)) = Nat.card (Component p f) := by
  apply Nat.card_congr
  apply componentEquiv p (splice f a b) p f
  intro x y
  rw [connected_splice_iff_of_seam p f (seam_of_fixed p f ha) x y]
  constructor
  · rintro (hxy | ⟨hxa, hyb⟩ | ⟨hxb, hya⟩)
    · exact hxy
    · exact hxa.trans (hab.trans hyb.symm)
    · exact hxb.trans (hab.symm.trans hya.symm)
  · exact Or.inl

theorem component_card_join_of_fixed [Finite D] (ha : f a = a)
    (hab : ¬ Connected p f a b) :
    Nat.card (Component p (splice f a b)) + 1 = Nat.card (Component p f) := by
  let : Fintype (Component p f) := Fintype.ofFinite _
  have he := Nat.card_congr (joinedComponentEquiv_of_seam p f (seam_of_fixed p f ha) hab)
  have hc := Fintype.card_subtype_compl (fun c : Component p f => c = component p f b)
  rw [Fintype.card_subtype_eq] at hc
  have hp : 0 < Fintype.card (Component p f) := Fintype.card_pos_iff.mpr ⟨component p f b⟩
  simp only [← Nat.card_eq_fintype_card] at hc hp
  change Nat.card {c : Component p f // c ≠ component p f b} = Nat.card (Component p f) - 1 at hc
  omega

end ThomGame.Pictures.RibbonConnectivity
