module

public import ThomGame.Pictures.RotationEulerGraph

/-!
# Deleting edges preserves Euler saturation

Deleting an edge fixes both of its ports and keeps the vertex rotation.
If the cut endpoints remain connected, the universal Euler bound forces
the count to stay unchanged. Otherwise the face and component counts
both split, preserving saturation. Iterating this operation allows any
pairing-invariant set of edges to be retained.
-/

@[expose] public section
namespace ThomGame.Pictures.RotationEuler

open Equiv CycleSurgery FiniteReturn RibbonConnectivity
open scoped Classical

variable {D : Type*} [Finite D] [DecidableEq D] (r t : Perm D)

theorem deleteEdge_saturated (ht : Function.Involutive t)
    (hEuler : count r t = 2 * Nat.card (Component r t)) (a : D) :
    count r (splice t a (t a)) = 2 * Nat.card (Component r (splice t a (t a))) := by
  by_cases ha : t a = a
  · have he : splice t a (t a) = t := by
      rw [ha, splice, swap_self]
      rfl
    simpa only [he] using hEuler
  let t₀ := splice t a (t a)
  have hfix : t₀ a = a := by simp [t₀, splice_apply]
  have he := count_splice r t₀ (Ne.symm ha) hfix
  change count r (splice (splice t a (t a)) a (t a)) = _ at he
  rw [splice_splice] at he
  have hb := count_le_twice_components r t₀ (removed_pair_involutive t ht a)
  by_cases hc : Connected r t₀ a (t a)
  · have hk := component_card_same_of_fixed r t₀ hfix hc
    change Nat.card (Component r (splice (splice t a (t a)) a (t a))) = _ at hk
    rw [splice_splice] at hk
    change count r t₀ = 2 * Nat.card (Component r t₀)
    split_ifs at he <;> omega
  · have hf : ¬ (t₀ * r).SameCycle a (t a) := fun h => hc (sameCycle_mul_connected r t₀ h)
    rw [ite_eq_right hf] at he
    have hk := component_card_join_of_fixed r t₀ hfix hc
    change Nat.card (Component r (splice (splice t a (t a)) a (t a))) + 1 = _ at hk
    rw [splice_splice] at hk
    change count r t₀ = 2 * Nat.card (Component r t₀)
    omega

variable (M : D → Prop) (hM : ∀ x, M (t x) ↔ M x)

noncomputable def retainEdges : Perm D where
  toFun x := if M x then t x else x
  invFun x := if M x then t.symm x else x
  left_inv x := by
    by_cases hx : M x
    · simp only [hx, (hM x).mpr hx, ite_true, Equiv.symm_apply_apply]
    · simp only [hx, ite_false]
  right_inv x := by
    by_cases hx : M x
    · have hi : M (t.symm x) := (hM (t.symm x)).mp (by simpa only [Equiv.apply_symm_apply] using hx)
      simp only [hx, hi, ite_true, Equiv.apply_symm_apply]
    · simp only [hx, ite_false]

omit [Finite D] [DecidableEq D] in
theorem retainEdges_apply (x : D) : retainEdges t M hM x = if M x then t x else x := rfl

omit [Finite D] [DecidableEq D] in
theorem retainEdges_involutive (ht : Function.Involutive t) :
    Function.Involutive (retainEdges t M hM) := by
  intro x
  by_cases hx : M x
  · simp only [retainEdges_apply, hx, (hM x).mpr hx, ite_true]
    exact ht x
  · simp only [retainEdges_apply, hx, ite_false]

omit [Finite D] in
include hM in
theorem deleteEdge_marking (a : D) (ha : ¬ M a) :
    ∀ x, M (splice t a (t a) x) ↔ M x := by
  intro x
  have hta : ¬ M (t a) := fun h => ha ((hM a).mp h)
  rw [splice_apply]
  by_cases hxa : t x = a
  · rw [hxa, swap_apply_left]
    have hx : ¬ M x := fun hx => ha (hxa ▸ (hM x).mpr hx)
    exact iff_of_false hta hx
  by_cases hxb : t x = t a
  · rw [hxb, swap_apply_right]
    have hx : ¬ M x := fun hx => hta (hxb ▸ (hM x).mpr hx)
    exact iff_of_false ha hx
  · rw [swap_apply_of_ne_of_ne hxa hxb]
    exact hM x

omit [Finite D] in
theorem retainEdges_deleteEdge (a : D) (ha : ¬ M a) :
    retainEdges (splice t a (t a)) M (deleteEdge_marking t M hM a ha) = retainEdges t M hM := by
  ext x
  simp only [retainEdges_apply]
  by_cases hx : M x
  · rw [ite_eq_left hx, ite_eq_left hx, splice_apply]
    apply swap_apply_of_ne_of_ne
    · intro he
      exact ha (he ▸ (hM x).mpr hx)
    · intro he
      exact ha ((hM a).mp (he ▸ (hM x).mpr hx))
  · rw [ite_eq_right hx, ite_eq_right hx]

include hM in
theorem retainEdges_saturated (ht : Function.Involutive t)
    (hEuler : count r t = 2 * Nat.card (Component r t)) :
    count r (retainEdges t M hM) = 2 * Nat.card (Component r (retainEdges t M hM)) := by
  let : Fintype D := Fintype.ofFinite D
  induction hn : t.support.card using Nat.strong_induction_on generalizing t with
  | h n ih =>
    by_cases hall : ∀ x, ¬ M x → t x = x
    · have he : retainEdges t M hM = t := by
        ext x
        rw [retainEdges_apply]
        by_cases hx : M x
        · rw [ite_eq_left hx]
        · rw [ite_eq_right hx, hall x hx]
      simpa only [he] using hEuler
    · obtain ⟨a, ha, hmove⟩ : ∃ a, ¬ M a ∧ t a ≠ a := by
        push Not at hall
        exact hall
      let t₀ := splice t a (t a)
      have hlt : t₀.support.card < n := by
        rw [← hn]
        exact Perm.card_support_swap_mul hmove
      have hs := ih t₀.support.card hlt t₀ (deleteEdge_marking t M hM a ha)
        (removed_pair_involutive t ht a) (deleteEdge_saturated r t ht hEuler a) rfl
      simpa only [t₀, retainEdges_deleteEdge t M hM a ha] using hs

end ThomGame.Pictures.RotationEuler
