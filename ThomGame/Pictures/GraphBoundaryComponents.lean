module

public import ThomGame.Pictures.GraphConnectivity
public import ThomGame.Pictures.ComponentSums
public import ThomGame.Pictures.BoundaryOrder
public import ThomGame.Pictures.CircuitComposition

/-!
# Boundary circuits and actual graph components

The boundary-component condition is translated into actual vertex
reachability. The five graph primitives and disjoint horizontal
composition satisfy it without geometric assumptions.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv RibbonConnectivity

variable {R S : Type*} {P : InvolutionPresentation R S} {u v w z : List S}

def BoundarySeesComponents (G : PortGraph P u v) : Prop :=
  SeesComponents G.pairing.perm G.circuitStep G.IsBoundary

theorem boundaryDart_vertex (G : PortGraph P u v) (i : BoundaryIndex u v) :
    (G.boundaryDart i).vertex = G.boundaryVertex i := by cases i <;> rfl

theorem boundary_leaves (G : PortGraph P u v) : Leaves G.pairing.perm G.circuitStep G.IsBoundary := by
  intro a ha
  change G.rotation (G.pairing.twin (G.pairing.twin a)) = a
  rw [G.pairing.involutive]
  cases a <;> first | rfl | exact ha.elim

theorem boundarySeesComponents_reachable (G : PortGraph P u v) (h : G.BoundarySeesComponents)
    (a b : BoundaryIndex u v) :
    G.Reachable (G.boundaryVertex a) (G.boundaryVertex b) ↔ G.boundaryNext.SameCycle a b := by
  have hv := G.connected_iff_vertex_reachable (G.boundaryDart a) (G.boundaryDart b)
  rw [G.boundaryDart_vertex, G.boundaryDart_vertex] at hv
  exact hv.symm.trans ((h (G.boundaryPorts a) (G.boundaryPorts b)).trans
    ((G.circuit_eq_iff _ _).symm.trans (G.boundaryNext_sameCycle_iff a b).symm))

theorem circuitStep_eq_pairing_of_no_internal (G : PortGraph P u v)
    [IsEmpty G.Hub] [IsEmpty G.Joint] : G.circuitStep = G.pairing.perm := by
  have hr : G.rotation = 1 := by
    ext a
    cases a with
    | top i => rfl
    | bottom i => rfl
    | hub h i => exact (isEmptyElim h : False).elim
    | joint j side => exact (isEmptyElim j : False).elim
  ext a
  change G.rotation (G.pairing.twin a) = G.pairing.twin a
  rw [hr]
  rfl

theorem boundarySeesComponents_of_no_internal (G : PortGraph P u v)
    [IsEmpty G.Hub] [IsEmpty G.Joint] : G.BoundarySeesComponents := by
  unfold BoundarySeesComponents
  rw [G.circuitStep_eq_pairing_of_no_internal]
  exact SeesComponents.self _ _

theorem boundarySeesComponents_of_one_cycle (G : PortGraph P u v)
    (h : ∀ a b, G.boundaryNext.SameCycle a b) : G.BoundarySeesComponents := by
  apply SeesComponents.of_one_cycle
  intro x y
  obtain ⟨a, rfl⟩ := G.boundaryPorts.surjective x
  obtain ⟨b, rfl⟩ := G.boundaryPorts.surjective y
  exact (G.circuit_eq_iff _ _).mp ((G.boundaryNext_sameCycle_iff a b).mp (h a b))

theorem boundarySeesComponents_identity (P : InvolutionPresentation R S) (w : List S) :
    (identity P w).BoundarySeesComponents := by
  let : IsEmpty (identity P w).Hub := by change IsEmpty Empty; infer_instance
  let : IsEmpty (identity P w).Joint := by change IsEmpty Empty; infer_instance
  exact boundarySeesComponents_of_no_internal _

theorem boundarySeesComponents_cap (P : InvolutionPresentation R S) (s : S) :
    (cap P s).BoundarySeesComponents := by
  let : IsEmpty (cap P s).Hub := by change IsEmpty Empty; infer_instance
  let : IsEmpty (cap P s).Joint := by change IsEmpty Empty; infer_instance
  exact boundarySeesComponents_of_no_internal _

theorem boundarySeesComponents_cup (P : InvolutionPresentation R S) (s : S) :
    (cup P s).BoundarySeesComponents := by
  let : IsEmpty (cup P s).Hub := by change IsEmpty Empty; infer_instance
  let : IsEmpty (cup P s).Joint := by change IsEmpty Empty; infer_instance
  exact boundarySeesComponents_of_no_internal _

theorem boundarySeesComponents_down (P : InvolutionPresentation R S) (r : R) :
    (down P r).BoundarySeesComponents := by
  apply boundarySeesComponents_of_one_cycle
  intro a b
  apply (FiniteReturn.sameCycle_congr _ _ (boundaryOrderIndex (P.word r) [])
    (down P r).numberedBoundaryNext_index a b).mpr
  rw [numberedBoundaryNext_down]
  exact finRotate_sameCycle _ _

theorem boundarySeesComponents_up (P : InvolutionPresentation R S) (r : R) :
    (up P r).BoundarySeesComponents := by
  apply boundarySeesComponents_of_one_cycle
  intro a b
  apply (FiniteReturn.sameCycle_congr _ _ (boundaryOrderIndex [] (P.word r))
    (up P r).numberedBoundaryNext_index a b).mpr
  rw [numberedBoundaryNext_up]
  exact finRotate_sameCycle _ _

theorem boundarySeesComponents_tensor (G : PortGraph P u v) (H : PortGraph P w z)
    (hG : G.BoundarySeesComponents) (hH : H.BoundarySeesComponents) :
    (G.tensor H).BoundarySeesComponents := by
  have hs := SeesComponents.sum G.pairing.perm G.circuitStep H.pairing.perm H.circuitStep hG hH
  apply hs.transport (tensorPorts G H) (twin_tensorPorts G H) (circuitStep_tensorPorts G H)
  rintro (a | a) <;> cases a <;> rfl

end ThomGame.Pictures.PortGraph
