module

public import ThomGame.Pictures.ComponentSurgery
public import ThomGame.Pictures.ReturnSurgery

/-!
# Boundary ports see one circuit in each component

`SeesComponents` is an explicit condition: among marked ports, graph
connectivity is exactly circuit connectivity. It is not built into the
definition of a graph or a component. A leaf splice preserves it when
same-circuit seam points are consecutive in the marked return order.
-/

@[expose] public section
namespace ThomGame.Pictures.RibbonConnectivity

open Equiv MarkedReturn CycleSurgery

variable {A B : Type*} [Finite A] [Finite B]

def SeesComponents (p f : Perm A) (M : A → Prop) : Prop :=
  ∀ x y : Subtype M, Connected p f x.val y.val ↔ f.SameCycle x.val y.val

def Leaves (p f : Perm A) (M : A → Prop) : Prop := ∀ x, M x → f (p x) = x

omit [Finite A] in
theorem SeesComponents.restrict {p f : Perm A} {M N : A → Prop}
    (h : SeesComponents p f M) (hNM : ∀ x, N x → M x) : SeesComponents p f N :=
  fun x y => h ⟨x.val, hNM x.val x.property⟩ ⟨y.val, hNM y.val y.property⟩

theorem SeesComponents.of_one_cycle (p f : Perm A) (M : A → Prop)
    (h : ∀ x y : Subtype M, f.SameCycle x.val y.val) : SeesComponents p f M :=
  fun x y => ⟨fun _ => h x y, sameCycle_connected p f⟩

theorem connected_self_iff_sameCycle (p : Perm A) (x y : A) :
    Connected p p x y ↔ p.SameCycle x y := by
  constructor
  · intro h
    apply h.lift (r := p.SameCycle) id ⟨(fun _ => Perm.SameCycle.rfl), Perm.SameCycle.symm, Perm.SameCycle.trans⟩
    · intro x; exact Perm.SameCycle.rfl.apply_right
    · intro x; exact Perm.SameCycle.rfl.apply_right
  · exact sameCycle_connected p p

theorem SeesComponents.self (p : Perm A) (M : A → Prop) : SeesComponents p p M :=
  fun x y => connected_self_iff_sameCycle p x.val y.val

theorem SeesComponents.transport {p f : Perm A} {q g : Perm B} {M : A → Prop} {N : B → Prop}
    (h : SeesComponents p f M) (e : A ≃ B)
    (hp : ∀ x, q (e x) = e (p x)) (hf : ∀ x, g (e x) = e (f x))
    (hMN : ∀ x, M x ↔ N (e x)) : SeesComponents q g N := by
  intro x y
  let x' : Subtype M := ⟨e.symm x.val, (hMN _).mpr (by simpa only [e.apply_symm_apply] using x.property)⟩
  let y' : Subtype M := ⟨e.symm y.val, (hMN _).mpr (by simpa only [e.apply_symm_apply] using y.property)⟩
  have hc := connected_congr p f q g e hp hf x'.val y'.val
  have hs := FiniteReturn.sameCycle_congr f g e hf x'.val y'.val
  simpa only [x', y', e.apply_symm_apply] using hc.symm.trans ((h x' y').trans hs)

variable [DecidableEq A]

theorem sameCycle_splice_marked_next (f : Perm A) (M : A → Prop) (a b x y : Subtype M)
    (hn : perm f M a = b) (hx : x ≠ a) (hy : y ≠ a) :
    (splice f a.val b.val).SameCycle x.val y.val ↔ f.SameCycle x.val y.val := by
  have hret := perm_splice_retained f M a b
  have hi := sameCycle_isolate_away_iff (perm f M) a hx hy
  change (splice (perm f M) a (perm f M a)).SameCycle x y ↔ (perm f M).SameCycle x y at hi
  rw [hn] at hi
  calc
    _ ↔ (perm (splice f a.val b.val) M).SameCycle x y := (sameCycle_iff _ M x y).symm
    _ ↔ (perm f M).SameCycle x y := by rw [hret]; exact hi
    _ ↔ _ := sameCycle_iff f M x y

/-- The exact component-to-boundary-circuit correspondence survives
deleting a seam whose equal-orbit case is consecutive on the boundary. -/
theorem SeesComponents.splice_restrict {p f : Perm A} {M N : A → Prop}
    (h : SeesComponents p f M) (a b : Subtype M)
    (ha : f (p a.val) = a.val) (hNM : ∀ x, N x → M x)
    (hNa : ¬ N a.val)
    (hn : f.SameCycle a.val b.val → perm f M a = b) :
    SeesComponents p (splice f a.val b.val) N := by
  intro x y
  let x' : Subtype M := ⟨x.val, hNM x.val x.property⟩
  let y' : Subtype M := ⟨y.val, hNM y.val y.property⟩
  by_cases hab : f.SameCycle a.val b.val
  · have hx : x' ≠ a := fun he => hNa ((congrArg Subtype.val he) ▸ x.property)
    have hy : y' ≠ a := fun he => hNa ((congrArg Subtype.val he) ▸ y.property)
    exact (connected_splice_iff_of_connected p f ha ((h a b).mpr hab) x.val y.val).trans
      ((h x' y').trans (sameCycle_splice_marked_next f M a b x' y' (hn hab) hx hy).symm)
  · exact (connected_splice_iff p f ha x.val y.val).trans
      ((or_congr (h x' y') (or_congr (and_congr (h x' a) (h y' b))
        (and_congr (h x' b) (h y' a)))).trans
        (sameCycle_join_iff f hab x.val y.val).symm)

omit [Finite A] in
theorem Leaves.splice_restrict {p f : Perm A} {M N : A → Prop}
    (h : Leaves p f M) (a b : A) (hNM : ∀ x, N x → M x) (ha : ¬ N a) (hb : ¬ N b) :
    Leaves p (splice f a b) N := by
  intro x hx
  rw [splice_apply, h x (hNM x hx)]
  exact swap_apply_of_ne_of_ne (fun he => ha (he ▸ hx)) (fun he => hb (he ▸ hx))

end ThomGame.Pictures.RibbonConnectivity
