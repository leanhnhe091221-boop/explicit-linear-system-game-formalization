module

public import ThomGame.Pictures.TwoStepReturn
public import ThomGame.Pictures.RibbonConnectivity

/-!
# Connectivity after suppressing fixed ports in a face walk

Every omitted port has its next face port retained, and the second
permutation fixes omitted ports. Project each omitted port onto that
next port. The projection transports full paths to the first-return
graph; expanding face returns gives the inverse connectivity statement.
-/

@[expose] public section
namespace ThomGame.Pictures.MarkedReturn

open Equiv RibbonConnectivity
open scoped Classical

variable {D : Type*} [Finite D] (f t : Perm D) (M : D → Prop)
  (ht : ∀ x, M (t x) ↔ M x) (hfix : ∀ x, ¬ M x → t x = x)
  (hstep : ∀ x, ¬ M x → M (f x))

noncomputable def stepProjection (x : D) : Subtype M :=
  if hx : M x then ⟨x, hx⟩ else ⟨f x, hstep x hx⟩

omit [Finite D] in
theorem stepProjection_kept (x : Subtype M) : stepProjection f M hstep x.val = x := by
  simp only [stepProjection, dite_eq_left x.property]

omit [Finite D] in
theorem stepProjection_omitted (x : D) (hx : ¬ M x) :
    (stepProjection f M hstep x).val = f x := by
  simp only [stepProjection, dite_eq_right hx]

theorem stepProjection_next (x : Subtype M) :
    stepProjection f M hstep (f x.val) = perm f M x := by
  apply Subtype.ext
  by_cases hx : M (f x.val)
  · rw [perm_val_of_step f M x hx]
    simp only [stepProjection, dite_eq_left hx]
  · rw [perm_val_of_two_steps f M x hx (hstep _ hx)]
    exact stepProjection_omitted f M hstep _ hx

theorem stepProjection_face (x : D) :
    Connected (perm f M) (t.subtypePerm ht)
      (stepProjection f M hstep x) (stepProjection f M hstep (f x)) := by
  by_cases hx : M x
  · have h₀ := stepProjection_kept f M hstep (⟨x, hx⟩ : Subtype M)
    have h₁ := stepProjection_next f M hstep (⟨x, hx⟩ : Subtype M)
    rw [h₀, h₁]
    exact Connected.edge _
  · have he : stepProjection f M hstep x = stepProjection f M hstep (f x) := by
      apply Subtype.ext
      simp only [stepProjection, dite_eq_right hx, dite_eq_left (hstep x hx)]
    rw [he]
    exact Connected.refl _

include hfix in
theorem stepProjection_edge (x : D) :
    Connected (perm f M) (t.subtypePerm ht)
      (stepProjection f M hstep x) (stepProjection f M hstep (t x)) := by
  by_cases hx : M x
  · have hy := (ht x).mpr hx
    rw [stepProjection_kept f M hstep (⟨x, hx⟩ : Subtype M),
      stepProjection_kept f M hstep (⟨t x, hy⟩ : Subtype M)]
    exact Connected.circuit _
  · rw [hfix x hx]
    exact Connected.refl _

include hfix hstep in
theorem connected_return_iff (x y : Subtype M) :
    Connected (perm f M) (t.subtypePerm ht) x y ↔ Connected f t x.val y.val := by
  constructor
  · intro h
    apply h.lift Subtype.val ⟨Connected.refl, Connected.symm, Connected.trans⟩
    · intro z
      exact (sameCycle_connected t f (perm_sameCycle f M z)).lift id
        ⟨Connected.refl, Connected.symm, Connected.trans⟩ Connected.circuit Connected.edge
    · intro z
      exact Connected.circuit z.val
  · intro h
    have hp := h.lift (stepProjection f M hstep) ⟨Connected.refl, Connected.symm, Connected.trans⟩
      (stepProjection_face f t M ht hstep) (stepProjection_edge f t M ht hfix hstep)
    simpa only [stepProjection_kept] using hp

omit [Finite D] in
theorem connected_stepProjection (x : D) :
    Connected f t x (stepProjection f M hstep x).val := by
  by_cases hx : M x
  · change Connected f t x (stepProjection f M hstep (⟨x, hx⟩ : Subtype M).val).val
    rw [stepProjection_kept]
    exact Connected.refl _
  · rw [stepProjection_omitted f M hstep x hx]
    exact Connected.edge _

include hfix in
theorem connected_projection_iff (x y : D) :
    Connected (perm f M) (t.subtypePerm ht)
      (stepProjection f M hstep x) (stepProjection f M hstep y) ↔ Connected f t x y := by
  rw [connected_return_iff f t M ht hfix hstep]
  constructor
  · intro h
    exact (connected_stepProjection f t M hstep x).trans
      (h.trans (connected_stepProjection f t M hstep y).symm)
  · intro h
    exact (connected_stepProjection f t M hstep x).symm.trans
      (h.trans (connected_stepProjection f t M hstep y))

/-- Suppressing these ports preserves every component, not just paths
between a separately assumed nonempty set of representatives. -/
noncomputable def returnComponentEquiv :
    Component (perm f M) (t.subtypePerm ht) ≃ Component f t where
  toFun := Quotient.lift (fun x => component f t x.val)
    (fun x y h => (component_eq_iff _ _ _ _).mpr
      ((connected_return_iff f t M ht hfix hstep x y).mp h))
  invFun := Quotient.lift (fun x => component (perm f M) (t.subtypePerm ht)
    (stepProjection f M hstep x))
    (fun x y h => (component_eq_iff _ _ _ _).mpr
      ((connected_projection_iff f t M ht hfix hstep x y).mpr h))
  left_inv c := Quotient.inductionOn c fun x => by
    change component _ _ (stepProjection f M hstep x.val) = component _ _ x
    rw [stepProjection_kept]
  right_inv c := Quotient.inductionOn c fun x =>
    (component_eq_iff _ _ _ _).mpr (connected_stepProjection f t M hstep x).symm

theorem returnComponentEquiv_apply (x : Subtype M) :
    returnComponentEquiv f t M ht hfix hstep (component _ _ x) = component f t x.val := rfl

include hfix hstep in
theorem return_component_card :
    Nat.card (Component (perm f M) (t.subtypePerm ht)) = Nat.card (Component f t) :=
  Nat.card_congr (returnComponentEquiv f t M ht hfix hstep)

end ThomGame.Pictures.MarkedReturn
