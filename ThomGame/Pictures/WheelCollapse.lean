module

public import ThomGame.Pictures.WheelCollapsedGraph
public import ThomGame.Pictures.WheelLiftOrientation
public import ThomGame.Pictures.DisconnectedClosedGraph

/-!
# Collapsing all facial wheel copies to original relation diagrams

The component quotient supplies disjoint actual wheel lifts. Facial
central and pentagon rims force uniform orientation on each lift.
The retained ordinary ports then form an actual original-presentation
graph with the same sign and saturated Euler count. Closed-graph
realization gives a diagram over the original presentation.
-/

@[expose] public section
namespace ThomGame.Wheel.Family

open Pictures PortGraph RibbonConnectivity

variable {R V R' V' : Type*} [DecidableEq R] [DecidableEq V]
  [DecidableEq R'] [DecidableEq V'] (F : Family R V)
  (rows : F.Row ≃ R') (cols : F.Col ≃ V')
  (G : SolutionGroup.RowGraph (F.system.reindex rows cols) [] []) [IsEmpty G.Joint]
  (hlen : ∀ r, 3 ≤ F.size r)
  (hb : ∀ (r : R) (a : G.RimDart (F.reindexedCentralCycle rows cols r (hlen r))),
    (∃ side, (G.rimSimpleCircuit _
      (F.reindexedCentralCycle rows cols r (hlen r)).empty_boundary_no_rim
      (F.reindexedCentralCycle rows cols r (hlen r)).empty_boundary_no_rim a).BoundsFaceOrbit side) ∧
    (G.rimSimpleCircuit _
      (F.reindexedCentralCycle rows cols r (hlen r)).empty_boundary_no_rim
      (F.reindexedCentralCycle rows cols r (hlen r)).empty_boundary_no_rim a).IsLabelCopy)
  (hp : ∀ (r : R) (j : Fin (F.size r))
      (a : G.RimDart (F.reindexedPentagonCycle rows cols r j)),
    (∃ side, (G.rimSimpleCircuit _
      (F.reindexedPentagonCycle rows cols r j).empty_boundary_no_rim
      (F.reindexedPentagonCycle rows cols r j).empty_boundary_no_rim a).BoundsFaceOrbit side) ∧
    (G.rimSimpleCircuit _
      (F.reindexedPentagonCycle rows cols r j).empty_boundary_no_rim
      (F.reindexedPentagonCycle rows cols r j).empty_boundary_no_rim a).IsLabelCopy)
  (he : eulerDefect G.pairing.perm G.circuitStep = 0)

include hb hp he in
theorem exists_collapsed_graph :
    ∃ K : PortGraph F.presentation [] [], IsEmpty K.Joint ∧
      eulerDefect K.pairing.perm K.circuitStep = 0 ∧ K.sign = G.sign := by
  let D := F.graphAtlasOfComponents rows cols G
    (F.every_hub_in_whole_wheel rows cols G hlen
      (fun r a => (hb r a).2) (fun r j a => (hp r j a).2))
  have hu (c : D.Component) (j : Fin (F.size (D.wheel c))) (k : Fin 3) :
      G.hubFlip ((D.lift c).hub j k) = G.hubFlip ((D.lift c).hub 0 0) :=
    (D.lift c).hubFlip_eq (hlen (D.wheel c))
      (fun a => (hb (D.wheel c) a).1) (fun i a => (hp (D.wheel c) i a).1) j 0 k 0
  exact ⟨D.collapsedGraph, (show IsEmpty Empty from inferInstance),
    D.collapsed_euler hu he, D.collapsed_sign⟩

include hb hp he in
theorem exists_collapsed_diagram :
    ∃ d : Diagram F.presentation [] [], d.sign = G.sign := by
  obtain ⟨K, _, hK, hs⟩ := F.exists_collapsed_graph rows cols G hlen hb hp he
  have hn (h : K.Hub) : 0 < (F.presentation.word (K.hubLabel h)).length := by
    change 0 < (List.ofFn (F.letter (K.hubLabel h))).length
    rw [List.length_ofFn]
    exact Nat.lt_of_lt_of_le (by decide : 0 < 2) (F.size_ge_two _)
  obtain ⟨d, _, _, hd⟩ := K.exists_closed_diagram_of_saturated_preserving hn
    (K.rotationEuler_saturated_iff.mpr hK)
  exact ⟨d, hd.trans hs⟩

end ThomGame.Wheel.Family
