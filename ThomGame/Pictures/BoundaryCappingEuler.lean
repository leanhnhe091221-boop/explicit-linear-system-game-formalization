module

public import ThomGame.Pictures.MarkedSurgery
public import ThomGame.Pictures.RotationEulerGraph

/-!
# Euler balance when boundary leaves become an outer vertex

At marked leaves the vertex rotation is the identity. Multiplying it by
the inverse boundary-return permutation merges these leaves into outer
vertices and splits the boundary faces. The two orbit changes cancel
exactly. This uses the actual first-return permutation, not an assumed
planar embedding.
-/

@[expose] public section
namespace ThomGame.Pictures.RotationEuler

open Equiv FiniteReturn MarkedReturn RibbonConnectivity

variable {D : Type*} [Finite D] (r t : Perm D) (M : D → Prop)
    (s : Perm D) (q : Perm (Subtype M))
    (hr : ∀ x, M x → r x = x)
    (hs : ∀ x, ¬ M x → s x = x)
    (hq : ∀ x : Subtype M, (q x).val = s x.val)

include hr in
theorem marked_rotation_eq_one : perm r M = 1 := by
  ext x
  have h : Hit r M x.val x.val := by
    have hd := Hit.direct (f := r) (p := M) x.val
    simpa only [hr x.val x.property] using hd
  exact (eq_perm_of_hit r M x x.property h).symm

include hr hs hq in
theorem count_cap_boundary (ht : Function.Involutive t)
    (hreturn : perm (r * t) M = q⁻¹) : count (s * r) t = count r t := by
  have hv := orbit_card_mul_balance r M s hs
  have hf := orbit_card_mul_balance (r * t) M s hs
  have hrv := perm_mul_retained r M s q hs hq
  have hrf := perm_mul_retained (r * t) M s q hs hq
  rw [marked_rotation_eq_one r M hr, mul_one] at hrv
  rw [hreturn, mul_inv_cancel] at hrf
  rw [marked_rotation_eq_one r M hr, hrv] at hv
  rw [hreturn, hrf] at hf
  have hqi : Nat.card (Orbit q⁻¹) = Nat.card (Orbit q) := by
    exact Nat.card_congr (Quotient.congrRight (fun _ _ => Perm.sameCycle_inv))
  have ha := Nat.card_congr (productOrbitEquiv r t ht)
  have hb := Nat.card_congr (productOrbitEquiv (s * r) t ht)
  rw [mul_assoc] at hb
  unfold count
  omega

omit [Finite D] in
include hr hs in
theorem connected_cap_boundary {x y : D} (h : Connected r t x y) :
    Connected (s * r) t x y := by
  classical
  apply h.lift id ⟨Connected.refl, Connected.symm, Connected.trans⟩
  · intro a
    by_cases ha : M a
    · change Connected (s * r) t a (r a)
      rw [hr a ha]
      exact Connected.refl a
    · have hn : ¬ M (r a) := by
        intro hm
        have he : r a = a := r.injective (hr (r a) hm)
        exact ha (he ▸ hm)
      have he : (s * r) a = r a := hs (r a) hn
      change Connected (s * r) t a (r a)
      simpa only [he] using (Connected.edge (p := s * r) (f := t) a)
  · intro a
    exact Connected.circuit a

end ThomGame.Pictures.RotationEuler
