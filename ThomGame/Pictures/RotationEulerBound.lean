module

public import ThomGame.Pictures.ComponentInsertion
public import ThomGame.Pictures.PrimitiveEuler

/-!
# Universal Euler upper bound for finite permutation maps

One permutation gives the cyclic orders at vertices, and an involution
gives edge pairings, possibly with fixed ports. The number of vertices,
edge orbits, and face orbits minus the dart count is at most twice the
number of connected components. The proof inserts actual disjoint edge
transpositions and counts the changes; no surface classification or
planarity assumption is used.
-/

@[expose] public section
namespace ThomGame.Pictures.RotationEuler

open Equiv CycleSurgery FiniteReturn RibbonConnectivity
open scoped Classical

variable {D : Type*} [Finite D] (r t : Perm D)

noncomputable def count : Int :=
  (Nat.card (Orbit r) : Int) + Nat.card (Orbit t) + Nat.card (Orbit (t * r)) - Nat.card D

theorem sameCycle_mul_connected {a b : D} (h : (t * r).SameCycle a b) : Connected r t a b := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => exact .refl _
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, Perm.mul_apply]
    exact ih.trans ((Connected.edge _).trans (Connected.circuit _))

theorem connected_one_iff (a b : D) : Connected r 1 a b ↔ r.SameCycle a b := by
  constructor
  · intro h
    apply h.lift id (Perm.SameCycle.equivalence r)
    · intro x
      exact ⟨1, by simp⟩
    · intro x
      exact Perm.SameCycle.rfl
  · intro h
    apply sameCycle_mul_connected r 1
    simpa only [one_mul] using h

def componentOneEquiv : Component r 1 ≃ Orbit r where
  toFun := Quotient.lift (orbit r)
    (fun a b h => (orbit_eq_iff r a b).mpr ((connected_one_iff r a b).mp h))
  invFun := Quotient.lift (component r 1)
    (fun a b h => (component_eq_iff r 1 a b).mpr ((connected_one_iff r a b).mpr h))
  left_inv c := Quotient.inductionOn c (fun _ => rfl)
  right_inv c := Quotient.inductionOn c (fun _ => rfl)

theorem count_one : count r 1 = 2 * Nat.card (Component r 1) := by
  have ho := Nat.card_congr (orbitOneEquiv D)
  have hc := Nat.card_congr (componentOneEquiv r)
  unfold count
  rw [one_mul, ho, hc]
  omega

variable [DecidableEq D]

theorem count_splice {a b : D} (hab : a ≠ b) (ha : t a = a) :
    count r (splice t a b) = count r t + if (t * r).SameCycle a b then 0 else -2 := by
  have he := orbit_card_join t (fun h => hab (h.eq_of_left ha))
  have hf := orbit_card_splice (t * r) hab
  unfold count
  rw [splice_mul]
  by_cases h : (t * r).SameCycle a b
  · rw [ite_eq_left h] at hf ⊢
    omega
  · rw [ite_eq_right h] at hf ⊢
    omega

theorem bound_splice_of_fixed {a b : D} (hab : a ≠ b) (ha : t a = a)
    (hb : count r t ≤ 2 * Nat.card (Component r t)) :
    count r (splice t a b) ≤ 2 * Nat.card (Component r (splice t a b)) := by
  have he := count_splice r t hab ha
  by_cases hc : Connected r t a b
  · rw [component_card_same_of_fixed r t ha hc]
    split_ifs at he <;> omega
  · have hf : ¬ (t * r).SameCycle a b := fun h => hc (sameCycle_mul_connected r t h)
    rw [ite_eq_right hf] at he
    have hk := component_card_join_of_fixed r t ha hc
    omega

omit [Finite D] in
theorem removed_pair_involutive (ht : Function.Involutive t) (a : D) :
    Function.Involutive (splice t a (t a)) := by
  intro x
  by_cases hxa : x = a
  · subst x
    simp [splice_apply]
  by_cases hxb : x = t a
  · subst x
    simp [splice_apply, ht a]
  have hta : t x ≠ a := by
    intro he
    exact hxb ((ht x).symm.trans (congrArg t he))
  have htb : t x ≠ t a := t.injective.ne hxa
  have hi : splice t a (t a) x = t x := by
    rw [splice_apply, swap_apply_of_ne_of_ne hta htb]
  rw [hi, splice_apply, ht x, swap_apply_of_ne_of_ne hxa hxb]

/-- This includes involutions with fixed ports, as needed after cutting
selected edges of a ribbon map. -/
theorem count_le_twice_components (ht : Function.Involutive t) :
    count r t ≤ 2 * Nat.card (Component r t) := by
  classical
  let : Fintype D := Fintype.ofFinite D
  induction hn : t.support.card using Nat.strong_induction_on generalizing t with
  | h n ih =>
    by_cases h1 : t = 1
    · subst t
      exact (count_one r).le
    have hs : t.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr
      (fun he => h1 (Perm.support_eq_empty_iff.mp he))
    obtain ⟨a, ha⟩ := hs
    have hm : t a ≠ a := Perm.mem_support.mp ha
    let t₀ := splice t a (t a)
    have hlt : t₀.support.card < n := by
      rw [← hn]
      exact Perm.card_support_swap_mul hm
    have hi := ih t₀.support.card hlt t₀ (removed_pair_involutive t ht a) rfl
    have hfix : t₀ a = a := by simp [t₀, splice_apply]
    have he := bound_splice_of_fixed r t₀ (Ne.symm hm) hfix hi
    simpa only [t₀, splice_splice] using he

end ThomGame.Pictures.RotationEuler
