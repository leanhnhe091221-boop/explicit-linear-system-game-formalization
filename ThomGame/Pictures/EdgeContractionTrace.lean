module

public import ThomGame.Pictures.EdgeContractionEuler

/-!
# A finite sequence of non-loop edge contractions

Every finite permutation map admits an explicit contraction trace ending
with one vertex orbit per original connected component. The remaining
edges are loops or fixed ports. Face permutation, Euler count, original
connectivity, and every uncontracted edge are preserved. This is a finite
combinatorial reduction, not yet a realization by diagram syntax.
-/

@[expose] public section
namespace ThomGame.Pictures

open Equiv CycleSurgery FiniteReturn RibbonConnectivity RotationEuler

universe u
variable {D : Type u} [DecidableEq D]

inductive EdgeContraction : Perm D → Perm D → Perm D → Perm D → Nat → Type u
  | refl (r t : Perm D) : EdgeContraction r t r t 0
  | step {r t r' t' : Perm D} {k : Nat} (a : D) (hr : ¬ r.SameCycle a (t a))
      (tail : EdgeContraction (splice r a (t a)) (splice t a (t a)) r' t' k) :
      EdgeContraction r t r' t' (k + 1)

namespace EdgeContraction

variable {r t r' t' : Perm D} {k : Nat}

theorem involutive (c : EdgeContraction r t r' t' k) :
    Function.Involutive t → Function.Involutive t' := by
  induction c with
  | refl => exact id
  | step a _ _ ih =>
    intro ht
    exact ih (removed_pair_involutive _ ht a)

theorem face_eq (c : EdgeContraction r t r' t' k) :
    Function.Involutive t → t' * r' = t * r := by
  induction c with
  | refl => intro _; rfl
  | step a _ _ ih =>
    intro ht
    exact (ih (removed_pair_involutive _ ht a)).trans (contractEdge_product _ _ ht a)

theorem removed_pair_value (t : Perm D) (ht : Function.Involutive t) (a x : D) :
    splice t a (t a) x = x ∨ splice t a (t a) x = t x := by
  by_cases hxa : x = a
  · subst x
    exact Or.inl (by simp [splice_apply])
  by_cases hxb : x = t a
  · subst x
    exact Or.inl (by simp [splice_apply, ht a])
  have hta : t x ≠ a := fun he => hxb ((ht x).symm.trans (congrArg t he))
  have htb : t x ≠ t a := t.injective.ne hxa
  exact Or.inr (swap_apply_of_ne_of_ne hta htb)

theorem edge_eq_or_fixed (c : EdgeContraction r t r' t' k) :
    Function.Involutive t → ∀ x, t' x = x ∨ t' x = t x := by
  induction c with
  | refl => intro _ x; exact Or.inr rfl
  | step a _ _ ih =>
    intro ht x
    rcases ih (removed_pair_involutive _ ht a) x with hx | hx
    · exact Or.inl hx
    · rcases removed_pair_value _ ht a x with he | he
      · exact Or.inl (hx.trans he)
      · exact Or.inr (hx.trans he)

theorem preserves_label {S : Type*} (c : EdgeContraction r t r' t' k)
    (ht : Function.Involutive t) (label : D → S) (hl : ∀ x, label (t x) = label x) (x : D) :
    label (t' x) = label x := by
  rcases c.edge_eq_or_fixed ht x with hx | hx
  · rw [hx]
  · rw [hx, hl]

variable [Finite D]

theorem connected_iff (c : EdgeContraction r t r' t' k) (x y : D) :
    Connected r' t' x y ↔ Connected r t x y := by
  induction c with
  | refl => rfl
  | step a hr _ ih => exact ih.trans (contractEdge_connected _ _ a hr x y)

theorem count_eq (c : EdgeContraction r t r' t' k) :
    Function.Involutive t → count r' t' = count r t := by
  induction c with
  | refl => intro _; rfl
  | step a hr _ ih =>
    intro ht
    exact (ih (removed_pair_involutive _ ht a)).trans (contractEdge_count _ _ ht a hr)

theorem component_card (c : EdgeContraction r t r' t' k) :
    Nat.card (Component r' t') = Nat.card (Component r t) :=
  Nat.card_congr (componentEquiv _ _ _ _ c.connected_iff)

theorem vertex_count (c : EdgeContraction r t r' t' k) :
    Nat.card (Orbit r') + k = Nat.card (Orbit r) := by
  induction c with
  | refl => omega
  | step a hr _ ih =>
    have hv := orbit_card_join _ hr
    omega

theorem saturated (c : EdgeContraction r t r' t' k) (ht : Function.Involutive t)
    (hEuler : count r t = 2 * Nat.card (Component r t)) :
    count r' t' = 2 * Nat.card (Component r' t') := by
  rw [c.count_eq ht, c.component_card, hEuler]

omit [DecidableEq D] in
theorem terminal_connected_iff (hterm : ∀ a, r'.SameCycle a (t' a)) (x y : D) :
    Connected r' t' x y ↔ r'.SameCycle x y := by
  constructor
  · intro h
    exact h.lift id (Perm.SameCycle.equivalence r')
      (fun _ => Perm.SameCycle.rfl.apply_right) hterm
  · intro h
    apply (connected_swap_iff _ _ _ _).mpr
    exact sameCycle_connected _ _ h

theorem terminal_original_connected (c : EdgeContraction r t r' t' k)
    (hterm : ∀ a, r'.SameCycle a (t' a)) (x y : D) :
    r'.SameCycle x y ↔ Connected r t x y :=
  (terminal_connected_iff hterm x y).symm.trans (c.connected_iff x y)

def terminalComponentEquiv (hterm : ∀ a, r'.SameCycle a (t' a)) :
    Component r' t' ≃ Orbit r' where
  toFun := Quotient.lift (orbit r') (fun a b hab =>
    (orbit_eq_iff r' a b).mpr ((terminal_connected_iff hterm a b).mp hab))
  invFun := Quotient.lift (component r' t') (fun a b hab =>
    (component_eq_iff r' t' a b).mpr ((terminal_connected_iff hterm a b).mpr hab))
  left_inv q := Quotient.inductionOn q (fun _ => rfl)
  right_inv q := Quotient.inductionOn q (fun _ => rfl)

theorem terminal_length (c : EdgeContraction r t r' t' k)
    (hterm : ∀ a, r'.SameCycle a (t' a)) :
    Nat.card (Component r t) + k = Nat.card (Orbit r) := by
  have hv := c.vertex_count
  have hc := Nat.card_congr (terminalComponentEquiv hterm)
  rw [c.component_card] at hc
  omega

/-- Repeatedly remove an actual edge between distinct current vertex orbits. -/
theorem exists_terminal (r t : Perm D) (ht : Function.Involutive t) :
    ∃ r' t' k, Nonempty (EdgeContraction r t r' t' k) ∧ ∀ a, r'.SameCycle a (t' a) := by
  classical
  let : Fintype D := Fintype.ofFinite D
  induction hn : t.support.card using Nat.strong_induction_on generalizing r t with
  | h n ih =>
    by_cases hterm : ∀ a, r.SameCycle a (t a)
    · exact ⟨r, t, 0, ⟨.refl r t⟩, hterm⟩
    push Not at hterm
    obtain ⟨a, ha⟩ := hterm
    have hm : t a ≠ a := fun he => ha (he.symm.sameCycle r)
    let t₀ := splice t a (t a)
    have hlt : t₀.support.card < n := by
      rw [← hn]
      exact Perm.card_support_swap_mul hm
    obtain ⟨r', t', k, ⟨tail⟩, hlast⟩ :=
      ih t₀.support.card hlt (splice r a (t a)) t₀ (removed_pair_involutive t ht a) rfl
    exact ⟨r', t', k + 1, ⟨.step a ha tail⟩, hlast⟩

end EdgeContraction
end ThomGame.Pictures
