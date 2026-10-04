module

public import ThomGame.Pictures.RowEdgeSwitch
public import ThomGame.Pictures.EdgeSwitchEuler
public import ThomGame.Pictures.ConnectedGraphRealization

/-! # Euler preservation for the actual row-graph edge switch -/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.RowEdgeSwitch

open Equiv RibbonConnectivity
open scoped Classical

variable {R S : Type*} {A : SparseSystem R S} {u v : List S}
  {G : SolutionGroup.RowGraph A u v} (s : G.RowEdgeSwitch)

theorem rotation_perm : s.graph.rotation = G.rotation := Equiv.ext s.rotation

theorem pairing_perm : s.graph.pairing.perm = s.portSwap * G.pairing.perm * s.portSwap := rfl

theorem distinct_vertices : s.first.vertex ≠ s.second.vertex := by
  intro he
  have hh : s.left = s.right := Sum.inl.inj (Sum.inr.inj he)
  exact s.first_ne_second (congrArg (fun h : G.Hub => (Port.hub h s.slot : G.Dart)) hh)

theorem eulerDefect_of_same_face
    (hEuler : eulerDefect G.pairing.perm G.circuitStep = 0)
    (hf : G.circuitStep.SameCycle s.first s.second) :
    eulerDefect s.graph.pairing.perm s.graph.circuitStep = 0 := by
  apply s.graph.rotationEuler_saturated_iff.mp
  rw [s.rotation_perm, s.pairing_perm]
  exact RotationEuler.switchEdges_saturated G.rotation G.pairing.perm G.pairing.involutive
    (G.rotationEuler_saturated_iff.mpr hEuler)
    (fun he => s.distinct_vertices ((G.rotation_sameCycle_iff _ _).mp he))
    (G.rotation_mul_pairing.symm ▸ hf)

theorem eulerDefect_of_twin_face
    (hEuler : eulerDefect G.pairing.perm G.circuitStep = 0)
    (hv : (G.pairing.twin s.first).vertex ≠ (G.pairing.twin s.second).vertex)
    (hf : G.circuitStep.SameCycle (G.pairing.twin s.first) (G.pairing.twin s.second)) :
    eulerDefect s.graph.pairing.perm s.graph.circuitStep = 0 := by
  have he := RotationEuler.switchEdges_saturated G.rotation G.pairing.perm G.pairing.involutive
    (G.rotationEuler_saturated_iff.mpr hEuler)
    (fun he => hv ((G.rotation_sameCycle_iff _ _).mp he))
    (G.rotation_mul_pairing.symm ▸ hf)
  have hp := RotationEuler.switchEdges_twins G.pairing.perm G.pairing.involutive
    (G.pairing.ne_self s.first) (G.pairing.ne_self s.second) s.first_ne_twin_second
  change swap (G.pairing.twin s.first) (G.pairing.twin s.second) * G.pairing.perm *
      swap (G.pairing.twin s.first) (G.pairing.twin s.second) = _ at hp
  rw [hp] at he
  apply s.graph.rotationEuler_saturated_iff.mp
  rw [s.rotation_perm, s.pairing_perm]
  exact he

end ThomGame.Pictures.PortGraph.RowEdgeSwitch
