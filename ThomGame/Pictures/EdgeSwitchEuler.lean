module

public import ThomGame.Pictures.VertexSplitEuler
public import ThomGame.Pictures.ConnectedResidualMatching

/-!
# Euler saturation of a same-face edge reconnection

The two attachments lie at distinct vertices and on a common face.
First join those vertices across that face, then split the resulting
vertex in the other order. Both steps preserve Euler saturation.
Conjugating all ports identifies the result with the actual switched
edge involution, with the original rotation unchanged.
-/

@[expose] public section
namespace ThomGame.Pictures.RotationEuler

open Equiv CycleSurgery FiniteReturn RibbonConnectivity
open scoped Classical

variable {D : Type*} [Finite D] [DecidableEq D] (r t : Perm D) {a b : D}

theorem joinVertex_sameFace_count (hr : ¬ r.SameCycle a b)
    (hf : (t * r).SameCycle (t a) (t b)) :
    count (splice r a b) t = count r t := by
  have hab : a ≠ b := fun he => hr (he ▸ Perm.SameCycle.rfl)
  have hv := orbit_card_join r hr
  have hc := orbit_card_split (t * r) (t.injective.ne hab) hf
  unfold count
  rw [splitVertex_product, hc]
  omega

theorem joinVertex_sameFace_component_card (hr : ¬ r.SameCycle a b)
    (hf : (t * r).SameCycle (t a) (t b)) :
    Nat.card (Component (splice r a b) t) = Nat.card (Component r t) := by
  have hs := sameCycle_connected t (splice r a b) (joins r hr)
  have hc : Connected r t a b :=
    (Connected.circuit a).trans
      ((sameCycle_mul_connected r t hf).trans (Connected.circuit b).symm)
  have he := component_card_same_of_seam t r hs ((connected_swap_iff r t a b).mp hc)
  rw [Nat.card_congr (componentEquiv t r r t (connected_swap_iff t r)),
    Nat.card_congr (componentEquiv t (splice r a b) (splice r a b) t
      (connected_swap_iff t (splice r a b)))] at he
  exact he

theorem joinVertex_sameFace_saturated
    (hEuler : count r t = 2 * Nat.card (Component r t))
    (hr : ¬ r.SameCycle a b) (hf : (t * r).SameCycle (t a) (t b)) :
    count (splice r a b) t = 2 * Nat.card (Component (splice r a b) t) := by
  rw [joinVertex_sameFace_count r t hr hf, joinVertex_sameFace_component_card r t hr hf]
  exact hEuler

theorem conjugateRotation_saturated (ht : Function.Involutive t)
    (hEuler : count r t = 2 * Nat.card (Component r t))
    (hr : ¬ r.SameCycle a b) (hf : (r * t).SameCycle a b) :
    count (swap a b * r * swap a b) t =
      2 * Nat.card (Component (swap a b * r * swap a b) t) := by
  have hf' : (t * r).SameCycle (t a) (t b) :=
    (sameCycle_congr (r * t) (t * r) t
      (fun _ => rfl) a b).mp hf
  let q := splice r a b
  have hq := joinVertex_sameFace_saturated r t hEuler hr hf'
  have hab : q.SameCycle (q a) (q b) := (joins r hr).apply_left.apply_right
  have he : splice q (q a) (q b) = swap a b * r * swap a b := by
    rw [splice, ← mul_swap_eq_swap_mul]
    rfl
  simpa only [he] using splitVertex_saturated q t ht hq hab

theorem switchEdges_saturated (ht : Function.Involutive t)
    (hEuler : count r t = 2 * Nat.card (Component r t))
    (hr : ¬ r.SameCycle a b) (hf : (r * t).SameCycle a b) :
    count r (swap a b * t * swap a b) =
      2 * Nat.card (Component r (swap a b * t * swap a b)) := by
  have he := conjugateRotation_saturated r t ht hEuler hr hf
  have hs (x : D) : (swap a b * r * swap a b) (swap a b x) = swap a b (r x) := by
    simp only [Perm.mul_apply, swap_apply_self]
  have hp (x : D) : t (swap a b x) = swap a b ((swap a b * t * swap a b) x) := by
    simp only [Perm.mul_apply, swap_apply_self]
  rw [count_congr r (swap a b * t * swap a b) (swap a b * r * swap a b) t
    (swap a b) hs hp,
    Nat.card_congr (componentCongrEquiv r (swap a b * t * swap a b)
      (swap a b * r * swap a b) t (swap a b) hs hp)]
  exact he

omit [Finite D] in
theorem switchEdges_twins (ht : Function.Involutive t)
    (ha : t a ≠ a) (hb : t b ≠ b) (hab : a ≠ t b) :
    swap (t a) (t b) * t * swap (t a) (t b) = swap a b * t * swap a b := by
  have hba : t a ≠ b := fun he => hab ((ht a).symm.trans (congrArg t he))
  have hcomm : swap a b * swap (t a) (t b) = swap (t a) (t b) * swap a b := by
    rw [mul_swap_eq_swap_mul, swap_apply_of_ne_of_ne ha hba,
      swap_apply_of_ne_of_ne hab.symm hb]
  have hts : t * swap (t a) (t b) = swap a b * t := by
    rw [mul_swap_eq_swap_mul, ht, ht]
  calc
    swap (t a) (t b) * t * swap (t a) (t b) =
        swap (t a) (t b) * swap a b * t := by rw [mul_assoc, hts, ← mul_assoc]
    _ = swap a b * swap (t a) (t b) * t := by rw [hcomm]
    _ = swap a b * t * swap a b := by rw [mul_assoc, ← mul_swap_eq_swap_mul, ← mul_assoc]

end ThomGame.Pictures.RotationEuler
