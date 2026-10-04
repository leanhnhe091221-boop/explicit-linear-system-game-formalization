module

public import ThomGame.Pictures.PairingCycleSeparation
public import ThomGame.Pictures.PairingCycleCounts
public import ThomGame.Pictures.RotationEulerGraph

/-! # Exact component counts for switching either pairing of a cycle graph -/

@[expose] public section
namespace ThomGame.Pictures.PairingCycles

open Equiv FiniteReturn RibbonConnectivity
open scoped Classical

variable {D E V : Type*} {edgeLabel : D → E} {vertexLabel : D → V}
  (p : Pairing edgeLabel) (q : Pairing vertexLabel) [Finite D]

theorem switchedVertex_component_card_split {a b : D} (hab : a ≠ b)
    (h : (walk p q).SameCycle a b) :
    Nat.card (Component p.perm (switchedVertex q a b).perm) =
      Nat.card (Component p.perm q.perm) + 1 := by
  have he := switchedWalk_orbit_card_split p q hab h
  rw [← walk_switchedVertex, walk_orbit_card, walk_orbit_card] at he
  omega

theorem switchedEdge_component_card_split {a b : D} (hab : a ≠ b)
    (h : (walk p q).SameCycle a b) :
    Nat.card (Component (switchedVertex p a b).perm q.perm) =
      Nat.card (Component p.perm q.perm) + 1 := by
  have he := switchedVertex_component_card_split q p hab h.inv
  rw [Nat.card_congr (componentEquiv q.perm p.perm p.perm q.perm
      (RotationEuler.connected_swap_iff q.perm p.perm)),
    Nat.card_congr (componentEquiv q.perm (switchedVertex p a b).perm
      (switchedVertex p a b).perm q.perm
      (RotationEuler.connected_swap_iff q.perm (switchedVertex p a b).perm))] at he
  exact he

theorem switchedVertex_component_card_join {a b : D} (h : ¬ Connected p.perm q.perm a b) :
    Nat.card (Component p.perm (switchedVertex q a b).perm) + 1 =
      Nat.card (Component p.perm q.perm) := by
  have he := switchedWalk_orbit_card_join p q h
  rw [← walk_switchedVertex, walk_orbit_card, walk_orbit_card] at he
  omega

theorem switchedEdge_component_card_join {a b : D} (h : ¬ Connected p.perm q.perm a b) :
    Nat.card (Component (switchedVertex p a b).perm q.perm) + 1 =
      Nat.card (Component p.perm q.perm) := by
  have he := switchedVertex_component_card_join q p
    (fun hc => h ((RotationEuler.connected_swap_iff q.perm p.perm a b).mp hc))
  rw [Nat.card_congr (componentEquiv q.perm p.perm p.perm q.perm
      (RotationEuler.connected_swap_iff q.perm p.perm)),
    Nat.card_congr (componentEquiv q.perm (switchedVertex p a b).perm
      (switchedVertex p a b).perm q.perm
      (RotationEuler.connected_swap_iff q.perm (switchedVertex p a b).perm))] at he
  exact he

theorem switchedEdge_connected {a b : D} (h : ¬ Connected p.perm q.perm a b) :
    Connected (switchedVertex p a b).perm q.perm a b :=
  (RotationEuler.connected_swap_iff q.perm (switchedVertex p a b).perm a b).mp
    (switched_joins q p (fun hc => h ((RotationEuler.connected_swap_iff q.perm p.perm a b).mp hc)))

end ThomGame.Pictures.PairingCycles
