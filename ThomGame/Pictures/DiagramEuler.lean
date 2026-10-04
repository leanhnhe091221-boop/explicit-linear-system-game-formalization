module

public import ThomGame.Pictures.DiagramBoundaryComponents
public import ThomGame.Pictures.CompositionEuler
public import ThomGame.Pictures.PrimitiveEuler

/-!
# Zero dart Euler defect for every actual diagram

Structural induction proves the integer identity for all diagrams,
including empty boundary words. For diagrams without zero-port hubs it
also gives the actual vertex/edge/circuit/component count. No surface
realization or geometric disk-face theorem is asserted here.
-/

@[expose] public section
namespace ThomGame.Pictures

open RibbonConnectivity

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}

theorem Diagram.graph_eulerDefect (d : Diagram P u v) :
    eulerDefect d.graph.pairing.perm d.graph.circuitStep = 0 := by
  induction d with
  | identity w => exact PortGraph.eulerDefect_identity P w
  | cap s => exact PortGraph.eulerDefect_cap P s
  | cup s => exact PortGraph.eulerDefect_cup P s
  | down r => exact PortGraph.eulerDefect_down P r
  | up r => exact PortGraph.eulerDefect_up P r
  | comp d e ihd ihe =>
    change eulerDefect (d.graph.comp e.graph).pairing.perm (d.graph.comp e.graph).circuitStep = 0
    rw [PortGraph.eulerDefect_comp d.graph e.graph d.graph_boundarySeesComponents
      e.graph_boundarySeesComponents d.graph_boundaryNoncrossing e.graph_boundaryNoncrossing, ihd, ihe]
    rfl
  | tensor d e ihd ihe =>
    change eulerDefect (d.graph.tensor e.graph).pairing.perm (d.graph.tensor e.graph).circuitStep = 0
    rw [PortGraph.eulerDefect_tensor, ihd, ihe]
    rfl

theorem Diagram.graph_ribbonEuler (d : Diagram P u v)
    (hn : ∀ h : d.graph.Hub, 0 < (P.word (d.graph.hubLabel h)).length) :
    d.graph.ribbonEuler = 2 * (Nat.card d.graph.GraphComponent : Int) := by
  have he := d.graph_eulerDefect
  rw [d.graph.eulerDefect_eq_ribbonEuler hn] at he
  omega

end ThomGame.Pictures
