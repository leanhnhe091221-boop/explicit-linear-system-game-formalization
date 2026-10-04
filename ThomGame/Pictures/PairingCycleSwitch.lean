module

public import ThomGame.Pictures.PairingCycles
public import ThomGame.Pictures.MarkedSurgery

/-!
# Splitting or joining both orientations of a paired cycle

Exchanging one port at each of two degree-two vertices conjugates the
vertex pairing. The alternating walk changes by two target exchanges.
When the selected ports lie on the same oriented cycle, both orientations
split; when their components differ, both orientations join. These are
exact orbit counts of the actual modified permutation.
-/

@[expose] public section
namespace ThomGame.Pictures.PairingCycles

open Equiv FiniteReturn MarkedReturn RibbonConnectivity CycleSurgery
open scoped Classical

variable {D E V : Type*} {edgeLabel : D → E} {vertexLabel : D → V}
  (p : Pairing edgeLabel) (q : Pairing vertexLabel) [Finite D]

theorem reverse_vertex_sameCycle {a b : D} (h : (walk p q).SameCycle a b) :
    (walk p q).SameCycle (q.twin a) (q.twin b) := by
  have h' : (walk q p).SameCycle a b := h.inv
  exact (reverse_sameCycle q p h').inv

noncomputable def switchedWalk (a b : D) : Perm D :=
  swap a b * swap (q.twin a) (q.twin b) * walk p q

omit [Finite D] in
theorem switchedWalk_vertex (a b : D) :
    switchedWalk p q a b = swap a b * q.perm * swap a b * p.perm := by
  ext x
  change swap a b (swap (q.twin a) (q.twin b) (q.twin (p.twin x))) =
    swap a b (q.twin (swap a b (p.twin x)))
  exact congrArg (swap a b) (q.perm.injective.map_swap a b (p.twin x)).symm

omit [Finite D] in
theorem switchedWalk_conjugate (a b : D) :
    swap a b * switchedWalk p q a b * swap a b =
      q.perm * swap a b * p.perm * swap a b := by
  rw [switchedWalk_vertex]
  simp only [← mul_assoc, swap_mul_self, one_mul]

theorem opposite_avoids_of_sameCycle {a b : D} (h : (walk p q).SameCycle a b) :
    Avoids (walk p q) (fun x => x = q.twin a ∨ x = q.twin b) a := by
  intro x hx hmark
  rcases hmark with rfl | rfl
  · exact not_sameCycle_vertex p q a hx
  · exact not_sameCycle_vertex p q b (h.symm.trans hx)

theorem opposite_avoids_of_disconnected {a b : D}
    (h : ¬ Connected p.perm q.perm a b) :
    Avoids (walk p q) (fun x => x = q.twin a ∨ x = q.twin b) a := by
  intro x hx hmark
  rcases hmark with rfl | rfl
  · exact not_sameCycle_vertex p q a hx
  · exact h ((sameCycle_connected p q hx).trans (Connected.circuit b).symm)

theorem firstSwap_sameCycle_iff {a b : D}
    (h : Avoids (walk p q) (fun x => x = q.twin a ∨ x = q.twin b) a) :
    (splice (walk p q) (q.twin a) (q.twin b)).SameCycle a b ↔ (walk p q).SameCycle a b := by
  apply sameCycle_mul_iff_of_avoids (walk p q) (fun x => x = q.twin a ∨ x = q.twin b)
    (swap (q.twin a) (q.twin b)) _ h b
  intro x hx
  exact swap_apply_of_ne_of_ne (fun ha => hx (Or.inl ha)) (fun hb => hx (Or.inr hb))

theorem switchedWalk_orbit_card_split {a b : D} (hab : a ≠ b)
    (h : (walk p q).SameCycle a b) :
    Nat.card (Orbit (switchedWalk p q a b)) = Nat.card (Orbit (walk p q)) + 2 := by
  have hq : q.twin a ≠ q.twin b := fun he => hab (q.perm.injective he)
  have h₁ := orbit_card_split (walk p q) hq (reverse_vertex_sameCycle p q h)
  have h₂ := orbit_card_split (splice (walk p q) (q.twin a) (q.twin b)) hab
    ((firstSwap_sameCycle_iff p q (opposite_avoids_of_sameCycle p q h)).mpr h)
  have he : switchedWalk p q a b = splice (splice (walk p q) (q.twin a) (q.twin b)) a b := by
    simp only [switchedWalk, splice, mul_assoc]
  rw [he, h₂, h₁]

theorem switchedWalk_orbit_card_join {a b : D} (h : ¬ Connected p.perm q.perm a b) :
    Nat.card (Orbit (switchedWalk p q a b)) + 2 = Nat.card (Orbit (walk p q)) := by
  have hn : ¬ (walk p q).SameCycle a b := fun he => h (sameCycle_connected p q he)
  have hnq : ¬ (walk p q).SameCycle (q.twin a) (q.twin b) := by
    intro he
    exact h ((Connected.circuit a).trans ((sameCycle_connected p q he).trans (Connected.circuit b).symm))
  have h₁ := orbit_card_join (walk p q) hnq
  have h₂ := orbit_card_join (splice (walk p q) (q.twin a) (q.twin b))
    (fun he => hn ((firstSwap_sameCycle_iff p q (opposite_avoids_of_disconnected p q h)).mp he))
  have he : switchedWalk p q a b = splice (splice (walk p q) (q.twin a) (q.twin b)) a b := by
    simp only [switchedWalk, splice, mul_assoc]
  rw [he]
  omega

end ThomGame.Pictures.PairingCycles
