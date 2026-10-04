module

public import ThomGame.Pictures.NestedReturn
public import Mathlib.Order.Circular.ZMod

/-!
# Ordered, noninterlacing circuit partitions

`Follows` says that the successor in each permutation orbit is its first
next point in the ambient cyclic order. `NonInterlacing` excludes four
cyclically ordered points belonging alternately to two different orbits.
Both properties survive restricting to marked points and taking genuine
first returns. They are explicit combinatorial conditions, not a claim
that a geometric disk realization has already been constructed.
-/

@[expose] public section
namespace ThomGame.Pictures.CircularPartition

open MarkedReturn

variable {A B : Type*}

/-- Each orbit follows the ambient successor without skipping another
point of that orbit. -/
def Follows (c f : Equiv.Perm A) : Prop :=
  ∀ x y, f.SameCycle x y → Hit c (fun z => f.SameCycle x z) y (f y)

/-- Alternating pairs in cyclic order must belong to a single orbit. -/
def NonInterlacing (o : A → A → A → Prop) (f : Equiv.Perm A) : Prop :=
  ∀ a b c d, o a b c → o a c d → f.SameCycle a c → f.SameCycle b d → f.SameCycle a b

structure OrderedNoncrossing (c : Equiv.Perm A) (o : A → A → A → Prop) (f : Equiv.Perm A) : Prop where
  follows : Follows c f
  noninterlacing : NonInterlacing o f

namespace Follows

variable {c f : Equiv.Perm A} (h : Follows c f)

include h

theorem at_self (x : A) : Hit c (f.SameCycle x) x (f x) := h x x Equiv.Perm.SameCycle.rfl

/-- Expand an `f`-path inside one orbit into the ambient cyclic order.
Only retained points of that orbit are marked in the resulting path. -/
theorem expand_return (p : A → Prop) (x : A) {y z : A}
    (hp : Hit f p y z) (hy : f.SameCycle x y) :
    Hit c (fun a => p a ∧ f.SameCycle x a) y z := by
  induction hp with
  | direct y => exact (h x y hy).weaken (fun _ ha => ha.2)
  | skip y hny tail ih =>
    have hstep : Hit c (fun a => p a ∧ f.SameCycle x a) y (f y) :=
      (h x y hy).weaken (fun _ ha => ha.2)
    exact hstep.append (fun ha => hny ha.1) (ih hy.apply_right)

variable [Finite A]

/-- Restricting both permutations retains the order of every remaining
orbit, including singleton orbits. -/
theorem restrict (p : A → Prop) : Follows (perm c p) (perm f p) := by
  intro x y hxy
  have hxy' : f.SameCycle x.val y.val := (sameCycle_iff f p x y).mp hxy
  let O : A → Prop := f.SameCycle x.val
  have hyO : O y.val := hxy'
  have hpath := h.expand_return p x.val (hit_perm f p y) hxy'
  have htarget : p (perm f p y).val ∧ O (perm f p y).val :=
    ⟨(perm f p y).property, hxy'.trans (perm_sameCycle f p y)⟩
  have he := eq_perm_of_hit c (fun a => p a ∧ O a)
    ⟨y.val, y.property, hyO⟩ htarget hpath
  have hn := perm_nested c p O ⟨y, hyO⟩
  have hv : (perm (perm c p) (fun a : Subtype p => O a.val) ⟨y, hyO⟩).val = perm f p y :=
    Subtype.ext (hn.trans he.symm)
  have hr := hit_perm (perm c p) (fun a : Subtype p => O a.val) ⟨y, hyO⟩
  rw [hv] at hr
  exact hr.weaken (fun a ha => (sameCycle_iff f p x a).mp ha)

omit [Finite A] in
theorem unique {g : Equiv.Perm A} (hg : Follows c g)
    (hfg : ∀ x y, f.SameCycle x y ↔ g.SameCycle x y) : f = g := by
  apply Equiv.ext
  intro x
  exact (h.at_self x).unique ((hg.at_self x).weaken (fun y hy => (hfg x y).mp hy))
    (Equiv.Perm.SameCycle.rfl.apply_right)
    ((hfg x (g x)).mpr Equiv.Perm.SameCycle.rfl.apply_right)

theorem transport [Finite B] {d g : Equiv.Perm B} (e : A ≃ B)
    (hc : ∀ a, d (e a) = e (c a)) (hf : ∀ a, g (e a) = e (f a)) : Follows d g := by
  intro x y hxy
  obtain ⟨x, rfl⟩ := e.surjective x
  obtain ⟨y, rfl⟩ := e.surjective y
  have hr := h x y ((FiniteReturn.sameCycle_congr f g e hf x y).mpr hxy)
  rw [hf]
  exact hr.map e hc (fun a => (FiniteReturn.sameCycle_congr f g e hf x a).symm)

end Follows

namespace NonInterlacing

variable {o : A → A → A → Prop} {f : Equiv.Perm A} (h : NonInterlacing o f)

include h

theorem no_alternating_orbits {a b c d : A} (habc : o a b c) (hacd : o a c d)
    (hac : f.SameCycle a c) (hbd : f.SameCycle b d) (hab : ¬ f.SameCycle a b) : False :=
  hab (h a b c d habc hacd hac hbd)

theorem pullback {B : Type*} {g : Equiv.Perm B} (e : B → A)
    (he : ∀ x y, g.SameCycle x y ↔ f.SameCycle (e x) (e y)) :
    NonInterlacing (fun a b c => o (e a) (e b) (e c)) g := by
  intro a b c d habc hacd hac hbd
  exact (he a b).mpr (h _ _ _ _ habc hacd ((he a c).mp hac) ((he b d).mp hbd))

theorem restrict [Finite A] (p : A → Prop) :
    NonInterlacing (fun a b c : Subtype p => o a.val b.val c.val) (perm f p) :=
  h.pullback Subtype.val (sameCycle_iff f p)

theorem transport [Finite A] [Finite B] {g : Equiv.Perm B} {o' : B → B → B → Prop}
    (e : A ≃ B) (hf : ∀ a, g (e a) = e (f a))
    (ho : ∀ a b c, o' (e a) (e b) (e c) ↔ o a b c) : NonInterlacing o' g := by
  intro a b c d habc hacd hac hbd
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  obtain ⟨c, rfl⟩ := e.surjective c
  obtain ⟨d, rfl⟩ := e.surjective d
  exact (FiniteReturn.sameCycle_congr f g e hf a b).mp
    (h a b c d ((ho _ _ _).mp habc) ((ho _ _ _).mp hacd)
      ((FiniteReturn.sameCycle_congr f g e hf a c).mpr hac)
      ((FiniteReturn.sameCycle_congr f g e hf b d).mpr hbd))

end NonInterlacing

namespace OrderedNoncrossing

variable {c f : Equiv.Perm A} {o : A → A → A → Prop}

theorem restrict [Finite A] (h : OrderedNoncrossing c o f) (p : A → Prop) :
    OrderedNoncrossing (perm c p) (fun a b c : Subtype p => o a.val b.val c.val) (perm f p) :=
  ⟨h.follows.restrict p, h.noninterlacing.restrict p⟩

theorem transport [Finite A] [Finite B] (h : OrderedNoncrossing c o f)
    {d g : Equiv.Perm B} {o' : B → B → B → Prop} (e : A ≃ B)
    (hc : ∀ a, d (e a) = e (c a)) (hf : ∀ a, g (e a) = e (f a))
    (ho : ∀ a b c, o' (e a) (e b) (e c) ↔ o a b c) : OrderedNoncrossing d o' g :=
  ⟨h.follows.transport e hc hf, h.noninterlacing.transport e hf ho⟩

end OrderedNoncrossing

theorem follows_self (c : Equiv.Perm A) : Follows c c := fun _ y _ => Hit.direct y

theorem noninterlacing_of_one_orbit (o : A → A → A → Prop) (f : Equiv.Perm A)
    (hf : ∀ a b, f.SameCycle a b) : NonInterlacing o f := fun a b _ _ _ _ _ _ => hf a b

theorem follows_one [Finite A] (c : Equiv.Perm A) : Follows c 1 := by
  intro x y hxy
  have hy : x = y := Equiv.Perm.sameCycle_one.mp hxy
  subst y
  have hr := hit_perm c (fun a => x = a) ⟨x, rfl⟩
  have hx := (perm c (fun a => x = a) ⟨x, rfl⟩).property
  rw [← hx] at hr
  exact hr.weaken (fun a ha => Equiv.Perm.sameCycle_one.mp ha)

theorem noninterlacing_one [CircularPreorder A] : NonInterlacing (sbtw : A → A → A → Prop) 1 := by
  intro a b c d habc _ hac _
  have he : a = c := Equiv.Perm.sameCycle_one.mp hac
  subst c
  exact (sbtw_irrefl_left_right habc).elim

end ThomGame.Pictures.CircularPartition
