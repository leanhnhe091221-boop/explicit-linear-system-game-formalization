module

public import ThomGame.Pictures.PairingCycleSwitch

/-!
# Actual component separation and joining under paired-cycle surgery

The split case refines both old oriented orbits and separates the two
selected vertices. The join case connects them. This records membership
information in addition to the orbit counts.
-/

@[expose] public section
namespace ThomGame.Pictures.PairingCycles

open Equiv FiniteReturn RibbonConnectivity CycleSurgery
open scoped Classical

variable {D E V : Type*} {edgeLabel : D → E} {vertexLabel : D → V}
  (p : Pairing edgeLabel) (q : Pairing vertexLabel) [Finite D]

noncomputable def switchedVertex (a b : D) : Pairing (fun x => vertexLabel (swap a b x)) :=
  q.transport (swap a b) _ (fun x => congrArg vertexLabel (swap_apply_self a b x))

omit [Finite D] in
theorem walk_switchedVertex (a b : D) : walk p (switchedVertex q a b) = switchedWalk p q a b := by
  rw [switchedWalk_vertex]
  rfl

theorem split_sameCycle_refines (f : Perm D) {a b x y : D} (hab : a ≠ b)
    (h : f.SameCycle a b) (hxy : (splice f a b).SameCycle x y) : f.SameCycle x y := by
  have he := oldCycle_in_join (splice f a b) (separates f hab h) hxy
  rwa [splice_splice] at he

theorem switchedWalk_refines {a b x y : D} (hab : a ≠ b) (h : (walk p q).SameCycle a b)
    (hxy : (switchedWalk p q a b).SameCycle x y) : (walk p q).SameCycle x y := by
  have hq : q.twin a ≠ q.twin b := fun he => hab (q.perm.injective he)
  have h₁ := (firstSwap_sameCycle_iff p q (opposite_avoids_of_sameCycle p q h)).mpr h
  have he : switchedWalk p q a b = splice (splice (walk p q) (q.twin a) (q.twin b)) a b := by
    simp only [switchedWalk, splice, mul_assoc]
  rw [he] at hxy
  exact split_sameCycle_refines (walk p q) hq (reverse_vertex_sameCycle p q h)
    (split_sameCycle_refines (splice (walk p q) (q.twin a) (q.twin b)) hab h₁ hxy)

theorem switched_separates {a b : D} (hab : a ≠ b) (h : (walk p q).SameCycle a b) :
    ¬ Connected p.perm (switchedVertex q a b).perm a b := by
  intro hc
  rcases (connected_iff p (switchedVertex q a b) a b).mp hc with hc | hc
  · rw [walk_switchedVertex] at hc
    have h₁ := (firstSwap_sameCycle_iff p q (opposite_avoids_of_sameCycle p q h)).mpr h
    have he : switchedWalk p q a b = splice (splice (walk p q) (q.twin a) (q.twin b)) a b := by
      simp only [switchedWalk, splice, mul_assoc]
    rw [he] at hc
    exact separates (splice (walk p q) (q.twin a) (q.twin b)) hab h₁ hc
  · rw [walk_switchedVertex] at hc
    exact not_sameCycle_edge p q a (h.trans (switchedWalk_refines p q hab h hc).symm)

theorem switched_joins {a b : D} (h : ¬ Connected p.perm q.perm a b) :
    Connected p.perm (switchedVertex q a b).perm a b := by
  apply sameCycle_connected
  rw [walk_switchedVertex]
  have hn : ¬ (walk p q).SameCycle a b := fun he => h (sameCycle_connected p q he)
  have h₁ : ¬ (splice (walk p q) (q.twin a) (q.twin b)).SameCycle a b :=
    fun he => hn ((firstSwap_sameCycle_iff p q (opposite_avoids_of_disconnected p q h)).mp he)
  have he : switchedWalk p q a b = splice (splice (walk p q) (q.twin a) (q.twin b)) a b := by
    simp only [switchedWalk, splice, mul_assoc]
  rw [he]
  exact joins _ h₁

theorem switchedWalk_away {a b x : D}
    (ha : ¬ Connected p.perm q.perm x a) (hb : ¬ Connected p.perm q.perm x b) (y : D) :
    (switchedWalk p q a b).SameCycle x y ↔ (walk p q).SameCycle x y := by
  let marked := fun z => z = a ∨ z = b ∨ z = q.twin a ∨ z = q.twin b
  have hs : ∀ z, ¬ marked z → (swap a b * swap (q.twin a) (q.twin b)) z = z := by
    intro z hz
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne
      (fun he => hz (Or.inr (Or.inr (Or.inl he))))
      (fun he => hz (Or.inr (Or.inr (Or.inr he)))),
      swap_apply_of_ne_of_ne (fun he => hz (Or.inl he)) (fun he => hz (Or.inr (Or.inl he)))]
  have hx : MarkedReturn.Avoids (walk p q) marked x := by
    intro z hz hm
    have hc := sameCycle_connected p q hz
    rcases hm with rfl | rfl | rfl | rfl
    · exact ha hc
    · exact hb hc
    · exact ha (hc.trans (Connected.circuit a).symm)
    · exact hb (hc.trans (Connected.circuit b).symm)
  exact MarkedReturn.sameCycle_mul_iff_of_avoids (walk p q) marked _ hs hx y

theorem switched_connected_away {a b x : D}
    (ha : ¬ Connected p.perm q.perm x a) (hb : ¬ Connected p.perm q.perm x b) (y : D) :
    Connected p.perm (switchedVertex q a b).perm x y ↔ Connected p.perm q.perm x y := by
  have hpa : ¬ Connected p.perm q.perm (p.twin x) a := fun h => ha ((Connected.edge x).trans h)
  have hpb : ¬ Connected p.perm q.perm (p.twin x) b := fun h => hb ((Connected.edge x).trans h)
  rw [connected_iff, connected_iff]
  change (walk p (switchedVertex q a b)).SameCycle x y ∨
      (walk p (switchedVertex q a b)).SameCycle (p.twin x) y ↔
    (walk p q).SameCycle x y ∨ (walk p q).SameCycle (p.twin x) y
  rw [walk_switchedVertex, switchedWalk_away p q ha hb y, switchedWalk_away p q hpa hpb y]

end ThomGame.Pictures.PairingCycles
