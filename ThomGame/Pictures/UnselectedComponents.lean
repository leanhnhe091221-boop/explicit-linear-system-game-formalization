module

public import ThomGame.Pictures.ComponentUnionSwitch

/-!
# Actual component quotients outside two selected roots

If the union of the selected components is unchanged and all paths from
unselected points are unchanged, the unselected component quotients are
in bijection. The map sends a component to the new component of any of
its original points; the representative formula proves this explicitly.
-/

@[expose] public section
namespace ThomGame.Pictures.RibbonConnectivity

open Equiv
open scoped Classical

variable {D : Type*} (p q r s : Perm D) (a b : D)

abbrev UnselectedComponent :=
  {c : Component p q // c ≠ component p q a ∧ c ≠ component p q b}

theorem unselected_out (c : UnselectedComponent p q a b) :
    ¬ Connected p q c.val.out a ∧ ¬ Connected p q c.val.out b := by
  have he : component p q c.val.out = c.val := Quotient.out_eq _
  exact ⟨fun h => c.property.1 (he.symm.trans ((component_eq_iff _ _ _ _).mpr h)),
    fun h => c.property.2 (he.symm.trans ((component_eq_iff _ _ _ _).mpr h))⟩

theorem away_iff_of_rootUnion
    (hroot : ∀ x, RootUnion p q a b x ↔ RootUnion r s a b x) (x : D) :
    (¬ Connected p q x a ∧ ¬ Connected p q x b) ↔
      (¬ Connected r s x a ∧ ¬ Connected r s x b) := by
  have h (f g : Perm D) : (¬ Connected f g x a ∧ ¬ Connected f g x b) ↔
      ¬ RootUnion f g a b x := by
    constructor
    · rintro ⟨ha, hb⟩ (hc | hc)
      · exact ha hc.symm
      · exact hb hc.symm
    · intro hn
      exact ⟨fun hc => hn (Or.inl hc.symm), fun hc => hn (Or.inr hc.symm)⟩
  exact (h p q).trans ((not_congr (hroot x)).trans (h r s).symm)

variable
  (haway : ∀ x, (¬ Connected p q x a ∧ ¬ Connected p q x b) ↔
    (¬ Connected r s x a ∧ ¬ Connected r s x b))
  (hpath : ∀ x, ¬ Connected p q x a → ¬ Connected p q x b →
    ∀ y, Connected r s x y ↔ Connected p q x y)

noncomputable def unselectedComponentMap :
    UnselectedComponent p q a b → UnselectedComponent r s a b := fun c =>
  ⟨component r s c.val.out, by
    have hn := (haway c.val.out).mp (unselected_out p q a b c)
    exact ⟨fun he => hn.1 ((component_eq_iff _ _ _ _).mp he),
      fun he => hn.2 ((component_eq_iff _ _ _ _).mp he)⟩⟩

include hpath in
theorem unselectedComponentMap_component (x : D)
    (hx : component p q x ≠ component p q a ∧ component p q x ≠ component p q b) :
    (unselectedComponentMap p q r s a b haway ⟨component p q x, hx⟩).val = component r s x := by
  have hn := unselected_out p q a b ⟨component p q x, hx⟩
  apply (component_eq_iff _ _ _ _).mpr
  exact (hpath _ hn.1 hn.2 x).mpr ((component_eq_iff _ _ _ _).mp (Quotient.out_eq _))

noncomputable def unselectedComponentEquiv :
    UnselectedComponent p q a b ≃ UnselectedComponent r s a b :=
  Equiv.ofBijective (unselectedComponentMap p q r s a b haway) ⟨by
    intro c d he
    have hn := unselected_out p q a b c
    have hp := (hpath _ hn.1 hn.2 d.val.out).mp
      ((component_eq_iff _ _ _ _).mp (congrArg Subtype.val he))
    apply Subtype.ext
    have hh := (component_eq_iff _ _ _ _).mpr hp
    exact (Quotient.out_eq c.val).symm.trans (hh.trans (Quotient.out_eq d.val)), by
    intro c
    have hn := (haway c.val.out).mpr (unselected_out r s a b c)
    have hx : component p q c.val.out ≠ component p q a ∧
        component p q c.val.out ≠ component p q b :=
      ⟨fun he => hn.1 ((component_eq_iff _ _ _ _).mp he),
        fun he => hn.2 ((component_eq_iff _ _ _ _).mp he)⟩
    refine ⟨⟨component p q c.val.out, hx⟩, ?_⟩
    apply Subtype.ext
    rw [unselectedComponentMap_component p q r s a b haway hpath]
    exact Quotient.out_eq _⟩

theorem unselectedComponentEquiv_component (x : D)
    (hx : component p q x ≠ component p q a ∧ component p q x ≠ component p q b) :
    (unselectedComponentEquiv p q r s a b haway hpath ⟨component p q x, hx⟩).val =
      component r s x :=
  unselectedComponentMap_component p q r s a b haway hpath x hx

end ThomGame.Pictures.RibbonConnectivity
