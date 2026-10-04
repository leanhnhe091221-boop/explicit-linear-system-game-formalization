module

public import ThomGame.Pictures.ComponentSurgery

/-!
# The integer Euler count under a leaf splice

This is a combinatorial count of rotation orbits, edge orbits, circuit
orbits and components. It is not yet identified with an embedded surface.
When the two boundary ports share a component exactly when they share a
circuit, a leaf splice preserves the count minus twice the components.
-/

@[expose] public section
namespace ThomGame.Pictures.RibbonConnectivity

open Equiv CycleSurgery FiniteReturn
open scoped Classical

variable {A : Type*} [Finite A] [DecidableEq A] (p f : Perm A)

/-- `f * p` is vertex rotation when `p` is the edge involution and `f`
is the circuit successor. Empty vertices have no orbit here. -/
noncomputable def eulerCount : Int :=
  (Nat.card (Orbit (f * p)) : Int) - Nat.card (Orbit p) + Nat.card (Orbit f)

noncomputable def eulerDefect : Int := eulerCount p f - 2 * Nat.card (Component p f)

omit [Finite A] in
theorem splice_mul (a b : A) : splice f a b * p = splice (f * p) a b := by
  simp only [splice, mul_assoc]

theorem rotation_card_leaf_splice {a b : A} (hab : a ≠ b)
    (ha : f (p a) = a) :
    Nat.card (Orbit (splice f a b * p)) + 1 = Nat.card (Orbit (f * p)) := by
  rw [splice_mul]
  apply orbit_card_join
  intro h
  exact hab (h.eq_of_left ha)

theorem eulerCount_leaf_splice {a b : A} (hab : a ≠ b)
    (ha : f (p a) = a) :
    eulerCount p (splice f a b) = eulerCount p f + if f.SameCycle a b then 0 else -2 := by
  classical
  have hv := rotation_card_leaf_splice p f hab ha
  have hc := orbit_card_splice f hab
  unfold eulerCount
  by_cases h : f.SameCycle a b
  · rw [ite_eq_left h] at hc ⊢
    omega
  · rw [ite_eq_right h] at hc ⊢
    omega

/-- Matching circuit/component information at the two leaves gives
the precise invariant needed for an eventual global Euler induction. -/
theorem eulerDefect_leaf_splice {a b : A} (hab : a ≠ b)
    (ha : f (p a) = a)
    (hsee : Connected p f a b ↔ f.SameCycle a b) :
    eulerDefect p (splice f a b) = eulerDefect p f := by
  have he := eulerCount_leaf_splice p f hab ha
  unfold eulerDefect
  by_cases hc : Connected p f a b
  · rw [ite_eq_left (hsee.mp hc)] at he
    rw [component_card_same p f ha hc]
    omega
  · have hn : ¬ f.SameCycle a b := fun h => hc (hsee.mpr h)
    rw [ite_eq_right hn] at he
    have hcard := component_card_join p f ha hc
    omega

end ThomGame.Pictures.RibbonConnectivity
