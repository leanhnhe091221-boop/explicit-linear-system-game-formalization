module

public import ThomGame.Pictures.RibbonConnectivity

/-!
# Component changes under an actual leaf-target exchange

The equation `f (p a) = a` means that `a` is a leaf for the rotation
`f * p` when `p` is edge reversal. It makes the exchanged endpoints
connected in the new graph and ensures that no old connection is lost.
The full new relation and the exact component counts are proved below.
-/

@[expose] public section
namespace ThomGame.Pictures.RibbonConnectivity

open Equiv CycleSurgery
open scoped Classical

variable {A : Type*} [DecidableEq A] (p f : Perm A) {a b : A}

theorem seam_connected (ha : f (p a) = a) : Connected p (splice f a b) a b := by
  have hs : splice f a b (p a) = b := by rw [splice_apply, ha, swap_apply_left]
  have hc : Connected p (splice f a b) (p a) (splice f a b (p a)) := Connected.circuit _
  rw [hs] at hc
  exact (Connected.edge a).trans hc

theorem old_connected_splice (ha : f (p a) = a) {x y : A} (hxy : Connected p f x y) :
    Connected p (splice f a b) x y := by
  have hab := seam_connected p f (b := b) ha
  apply hxy.lift id ⟨Connected.refl, Connected.symm, Connected.trans⟩
  · exact Connected.edge
  · intro x
    change Connected p (splice f a b) x (f x)
    have hx : Connected p (splice f a b) x (splice f a b x) := Connected.circuit _
    by_cases hxa : f x = a
    · rw [splice_apply, hxa, swap_apply_left] at hx
      rw [hxa]
      exact hx.trans hab.symm
    by_cases hxb : f x = b
    · rw [splice_apply, hxb, swap_apply_right] at hx
      rw [hxb]
      exact hx.trans hab
    · rw [splice_apply, swap_apply_of_ne_of_ne hxa hxb] at hx
      exact hx

noncomputable def mergedClass (a b x : A) : Component p f :=
  if component p f x = component p f b then component p f a else component p f x

omit [DecidableEq A] in
theorem mergedClass_edge (a b x : A) : mergedClass p f a b (p x) = mergedClass p f a b x := by
  simp only [mergedClass, component_edge]

theorem mergedClass_splice (a b x : A) :
    mergedClass p f a b (splice f a b x) = mergedClass p f a b x := by
  unfold mergedClass
  rw [splice_apply, ← component_circuit p f x]
  by_cases hxa : f x = a
  · rw [hxa, swap_apply_left]
    simp
  by_cases hxb : f x = b
  · rw [hxb, swap_apply_right]
    simp
  · rw [swap_apply_of_ne_of_ne hxa hxb]

omit [DecidableEq A] in
theorem rel_of_mergedClass_eq {x y : A} (he : mergedClass p f a b x = mergedClass p f a b y) :
    Connected p f x y ∨ (Connected p f x a ∧ Connected p f y b) ∨
      (Connected p f x b ∧ Connected p f y a) := by
  unfold mergedClass at he
  split_ifs at he with hx hy hy
  · exact Or.inl (((component_eq_iff p f x b).mp hx).trans
      ((component_eq_iff p f y b).mp hy).symm)
  · exact Or.inr (Or.inr ⟨(component_eq_iff p f x b).mp hx,
      ((component_eq_iff p f a y).mp he).symm⟩)
  · exact Or.inr (Or.inl ⟨(component_eq_iff p f x a).mp he,
      (component_eq_iff p f y b).mp hy⟩)
  · exact Or.inl ((component_eq_iff p f x y).mp he)

/-- A leaf splice merges precisely the two endpoint components. -/
theorem connected_splice_iff (ha : f (p a) = a) (x y : A) :
    Connected p (splice f a b) x y ↔ Connected p f x y ∨
      (Connected p f x a ∧ Connected p f y b) ∨
      (Connected p f x b ∧ Connected p f y a) := by
  constructor
  · intro hxy
    exact rel_of_mergedClass_eq p f
      (hxy.invariant (mergedClass p f a b) (mergedClass_edge p f a b) (mergedClass_splice p f a b))
  · rintro (hxy | ⟨hxa, hyb⟩ | ⟨hxb, hya⟩)
    · exact old_connected_splice p f ha hxy
    · exact (old_connected_splice p f ha hxa).trans
        ((seam_connected p f ha).trans (old_connected_splice p f ha hyb).symm)
    · exact (old_connected_splice p f ha hxb).trans
        ((seam_connected p f ha).symm.trans (old_connected_splice p f ha hya).symm)

theorem connected_splice_iff_of_connected (ha : f (p a) = a) (hab : Connected p f a b)
    (x y : A) : Connected p (splice f a b) x y ↔ Connected p f x y := by
  rw [connected_splice_iff p f ha x y]
  constructor
  · rintro (hxy | ⟨hxa, hyb⟩ | ⟨hxb, hya⟩)
    · exact hxy
    · exact hxa.trans (hab.trans hyb.symm)
    · exact hxb.trans (hab.symm.trans hya.symm)
  · exact Or.inl

def componentEquiv (q g : Perm A)
    (h : ∀ x y, Connected p f x y ↔ Connected q g x y) : Component p f ≃ Component q g where
  toFun := Quotient.lift (component q g) (fun x y hxy => (component_eq_iff q g x y).mpr ((h x y).mp hxy))
  invFun := Quotient.lift (component p f) (fun x y hxy => (component_eq_iff p f x y).mpr ((h x y).mpr hxy))
  left_inv c := Quotient.inductionOn c (fun _ => rfl)
  right_inv c := Quotient.inductionOn c (fun _ => rfl)

noncomputable def mergeComponent (a b : A) : Component p (splice f a b) → Component p f :=
  Quotient.lift (mergedClass p f a b) (fun _ _ h =>
    Connected.invariant (mergedClass p f a b) (mergedClass_edge p f a b) (mergedClass_splice p f a b) h)

theorem mergeComponent_injective (ha : f (p a) = a) : Function.Injective (mergeComponent p f a b) := by
  intro c d hcd
  refine Quotient.inductionOn₂ c d (fun x y he => ?_) hcd
  apply (component_eq_iff p (splice f a b) x y).mpr
  apply (connected_splice_iff p f ha x y).mpr
  exact rel_of_mergedClass_eq p f he

theorem mergeComponent_ne (hab : ¬ Connected p f a b) (c : Component p (splice f a b)) :
    mergeComponent p f a b c ≠ component p f b := by
  have hab' : component p f a ≠ component p f b := fun he => hab ((component_eq_iff p f a b).mp he)
  refine Quotient.inductionOn c fun x => ?_
  change mergedClass p f a b x ≠ component p f b
  unfold mergedClass
  split_ifs with hx
  · exact hab'
  · exact hx

/-- When the old components are different, the new components are
exactly the old ones with the class of `b` identified with that of `a`. -/
noncomputable def joinedComponentEquiv (ha : f (p a) = a) (hab : ¬ Connected p f a b) :
    Component p (splice f a b) ≃ {c : Component p f // c ≠ component p f b} :=
  Equiv.ofBijective (fun c => ⟨mergeComponent p f a b c, mergeComponent_ne p f hab c⟩) ⟨by
    intro c d hcd
    exact mergeComponent_injective p f ha (congrArg Subtype.val hcd), by
    rintro ⟨c, hc⟩
    refine Quotient.inductionOn c (fun x hx => ?_) hc
    change component p f x ≠ component p f b at hx
    refine ⟨component p (splice f a b) x, Subtype.ext ?_⟩
    change mergedClass p f a b x = component p f x
    simp only [mergedClass, ite_eq_right hx]⟩

variable [Finite A]

theorem component_card_join (ha : f (p a) = a) (hab : ¬ Connected p f a b) :
    Nat.card (Component p (splice f a b)) + 1 = Nat.card (Component p f) := by
  let : Fintype (Component p f) := Fintype.ofFinite _
  have he := Nat.card_congr (joinedComponentEquiv p f ha hab)
  have hc := Fintype.card_subtype_compl (fun c : Component p f => c = component p f b)
  rw [Fintype.card_subtype_eq] at hc
  have hp : 0 < Fintype.card (Component p f) := Fintype.card_pos_iff.mpr ⟨component p f b⟩
  simp only [← Nat.card_eq_fintype_card] at hc hp
  change Nat.card {c : Component p f // c ≠ component p f b} = Nat.card (Component p f) - 1 at hc
  omega

omit [Finite A] in
theorem component_card_same (ha : f (p a) = a) (hab : Connected p f a b) :
    Nat.card (Component p (splice f a b)) = Nat.card (Component p f) :=
  Nat.card_congr (componentEquiv p (splice f a b) p f (connected_splice_iff_of_connected p f ha hab))

end ThomGame.Pictures.RibbonConnectivity
