module

public import ThomGame.Pictures.RibbonConnectivity

/-!
# Lifting paths inside an invariant set

A map defined only on an invariant set can still transport every path
whose endpoints lie there. The proof extends the map by one endpoint
outside the set; invariance makes both generators preserve the two cases.
-/

@[expose] public section
namespace ThomGame.Pictures.RibbonConnectivity.Connected

open Equiv

variable {A B : Type*} {p f : Perm A} {x y : A}

theorem lift_restricted (h : Connected p f x y) (M : A → Prop)
    (hp : ∀ a, M (p a) ↔ M a) (hf : ∀ a, M (f a) ↔ M a)
    (hx : M x) (hy : M y) (e : Subtype M → B)
    {r : B → B → Prop} (hr : Equivalence r)
    (ep : ∀ a : Subtype M, r (e a) (e ⟨p a.val, (hp a.val).mpr a.property⟩))
    (ef : ∀ a : Subtype M, r (e a) (e ⟨f a.val, (hf a.val).mpr a.property⟩)) :
    r (e ⟨x, hx⟩) (e ⟨y, hy⟩) := by
  classical
  let g (a : A) : B := if ha : M a then e ⟨a, ha⟩ else e ⟨x, hx⟩
  have hpg (a : A) : r (g a) (g (p a)) := by
    by_cases ha : M a
    · have hb := (hp a).mpr ha
      simpa only [g, dite_eq_left ha, dite_eq_left hb] using ep ⟨a, ha⟩
    · have hb : ¬ M (p a) := fun hb => ha ((hp a).mp hb)
      simp only [g, dite_eq_right ha, dite_eq_right hb]
      exact hr.refl _
  have hfg (a : A) : r (g a) (g (f a)) := by
    by_cases ha : M a
    · have hb := (hf a).mpr ha
      simpa only [g, dite_eq_left ha, dite_eq_left hb] using ef ⟨a, ha⟩
    · have hb : ¬ M (f a) := fun hb => ha ((hf a).mp hb)
      simp only [g, dite_eq_right ha, dite_eq_right hb]
      exact hr.refl _
  simpa only [g, dite_eq_left hx, dite_eq_left hy] using h.lift g hr hpg hfg

end ThomGame.Pictures.RibbonConnectivity.Connected
