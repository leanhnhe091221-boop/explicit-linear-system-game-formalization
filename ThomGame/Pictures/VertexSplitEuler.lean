module

public import ThomGame.Pictures.RotationEulerGraph

/-!
# Splitting a vertex preserves Euler saturation

Exchanging two targets in one vertex cycle splits that cycle into two
contiguous blocks. The graph either stays connected across the cut or
splits one component in two. In the latter case the face count also
increases by one. Neither connectivity nor the face permutation is
asserted to remain unchanged.
-/

@[expose] public section
namespace ThomGame.Pictures

open Equiv CycleSurgery FiniteReturn
open scoped Classical

namespace RibbonConnectivity

variable {D : Type*} [DecidableEq D] (p f : Perm D) {a b : D}

theorem component_card_same_of_seam (hs : Connected p (splice f a b) a b)
    (hab : Connected p f a b) :
    Nat.card (Component p (splice f a b)) = Nat.card (Component p f) := by
  apply Nat.card_congr
  apply componentEquiv p (splice f a b) p f
  intro x y
  rw [connected_splice_iff_of_seam p f hs x y]
  constructor
  · rintro (hxy | ⟨hxa, hyb⟩ | ⟨hxb, hya⟩)
    · exact hxy
    · exact hxa.trans (hab.trans hyb.symm)
    · exact hxb.trans (hab.symm.trans hya.symm)
  · exact Or.inl

theorem component_card_join_of_seam [Finite D]
    (hs : Connected p (splice f a b) a b) (hab : ¬ Connected p f a b) :
    Nat.card (Component p (splice f a b)) + 1 = Nat.card (Component p f) := by
  let : Fintype (Component p f) := Fintype.ofFinite _
  have he := Nat.card_congr (joinedComponentEquiv_of_seam p f hs hab)
  have hc := Fintype.card_subtype_compl (fun c : Component p f => c = component p f b)
  rw [Fintype.card_subtype_eq] at hc
  have hp : 0 < Fintype.card (Component p f) := Fintype.card_pos_iff.mpr ⟨component p f b⟩
  simp only [← Nat.card_eq_fintype_card] at hc hp
  change Nat.card {c : Component p f // c ≠ component p f b} = Nat.card (Component p f) - 1 at hc
  omega

end RibbonConnectivity

namespace RotationEuler

open RibbonConnectivity

variable {D : Type*} [Finite D] [DecidableEq D] (r t : Perm D) {a b : D}

omit [Finite D] in
theorem splitVertex_product : t * splice r a b = splice (t * r) (t a) (t b) := by
  rw [splice, splice, ← mul_assoc, mul_swap_eq_swap_mul, mul_assoc]

theorem splitVertex_count (hab : a ≠ b) (hr : r.SameCycle a b) :
    count (splice r a b) t =
      count r t + if (t * r).SameCycle (t a) (t b) then 2 else 0 := by
  have hv := orbit_card_split r hab hr
  have hf := orbit_card_splice (t * r) (t.injective.ne hab)
  unfold count
  rw [splitVertex_product]
  split_ifs at hf ⊢ <;> omega

theorem splitVertex_component_card (hr : r.SameCycle a b) :
    Nat.card (Component (splice r a b) t) = Nat.card (Component r t) +
      if Connected (splice r a b) t a b then 0 else 1 := by
  have hs : Connected t (splice (splice r a b) a b) a b := by
    rw [splice_splice]
    exact sameCycle_connected t r hr
  have hOld := Nat.card_congr (componentEquiv t r r t (connected_swap_iff t r))
  have hNew := Nat.card_congr (componentEquiv t (splice r a b) (splice r a b) t
    (connected_swap_iff t (splice r a b)))
  by_cases hc : Connected (splice r a b) t a b
  · have he := component_card_same_of_seam t (splice r a b) hs
      ((connected_swap_iff _ _ _ _).mp hc)
    rw [splice_splice] at he
    rw [ite_eq_left hc]
    omega
  · have he := component_card_join_of_seam t (splice r a b) hs
      (fun h => hc ((connected_swap_iff _ _ _ _).mp h))
    rw [splice_splice] at he
    rw [ite_eq_right hc]
    omega

theorem splitVertex_saturated (ht : Function.Involutive t)
    (hEuler : count r t = 2 * Nat.card (Component r t))
    (hr : r.SameCycle a b) :
    count (splice r a b) t = 2 * Nat.card (Component (splice r a b) t) := by
  by_cases hab : a = b
  · subst b
    have he : splice r a a = r := by ext x; simp [splice_apply]
    simpa only [he] using hEuler
  have he := splitVertex_count r t hab hr
  have hk := splitVertex_component_card r t hr
  by_cases hc : Connected (splice r a b) t a b
  · rw [ite_eq_left hc] at hk
    have hb := count_le_twice_components (splice r a b) t ht
    split_ifs at he <;> omega
  · rw [ite_eq_right hc] at hk
    have hn : ¬ (t * splice r a b).SameCycle (t a) (t b) := by
      intro hf
      have hh := sameCycle_mul_connected (splice r a b) t hf
      exact hc ((Connected.circuit a).trans (hh.trans (Connected.circuit b).symm))
    rw [splitVertex_product] at hn
    have hf : (t * r).SameCycle (t a) (t b) := by
      by_contra hf
      exact hn (joins (t * r) hf)
    rw [ite_eq_left hf] at he
    omega

end RotationEuler
end ThomGame.Pictures
