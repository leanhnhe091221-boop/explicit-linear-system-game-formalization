module

public import ThomGame.Pictures.GraphPrimitives

/-!
# Extracting a finite graph from a diagram

Relation vertices are in bijection with the exact ordered relation-use list.
Boundary vertices have degree one, hubs have the length of their actual word,
and the only extra vertices are degree-two seams. This is an incidence-level
interpretation, not yet a planar embedding or a constellation theorem.
-/

@[expose] public section
namespace ThomGame.Pictures

open scoped BigOperators

variable {R S : Type*} {P : InvolutionPresentation R S}

namespace PortGraph

variable {u v w z : List S}

def sign (G : PortGraph P u v) : ZMod 2 := ∑ h, P.parity (G.hubLabel h)

theorem sign_comp (G : PortGraph P u v) (H : PortGraph P v w) :
    (G.comp H).sign = G.sign + H.sign := by
  change (∑ h : G.Hub ⊕ H.Hub, P.parity (Sum.elim G.hubLabel H.hubLabel h)) = _
  rw [Fintype.sum_sum_type]
  rfl

theorem sign_tensor (G : PortGraph P u v) (H : PortGraph P w z) :
    (G.tensor H).sign = G.sign + H.sign := by
  change (∑ h : G.Hub ⊕ H.Hub, P.parity (Sum.elim G.hubLabel H.hubLabel h)) = _
  rw [Fintype.sum_sum_type]
  rfl

end PortGraph

namespace Diagram

variable {u v : List S}

def graph : {u v : List S} → Diagram P u v → PortGraph P u v
  | _, _, .identity w => PortGraph.identity P w
  | _, _, .cap s => PortGraph.cap P s
  | _, _, .cup s => PortGraph.cup P s
  | _, _, .down r => PortGraph.down P r
  | _, _, .up r => PortGraph.up P r
  | _, _, .comp d e => d.graph.comp e.graph
  | _, _, .tensor d e => d.graph.tensor e.graph

def emptyIndex : Empty ≃ Fin 0 where
  toFun := Empty.elim
  invFun := Fin.elim0
  left_inv a := a.elim
  right_inv a := Fin.elim0 a

def unitIndex : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv a := by cases a; rfl
  right_inv a := Subsingleton.elim _ _

/-- Each relation vertex is exactly one occurrence in the diagram's label list. -/
def hubIndex : {u v : List S} → (d : Diagram P u v) → d.graph.Hub ≃ Fin d.labels.length
  | _, _, .identity _ => emptyIndex
  | _, _, .cap _ => emptyIndex
  | _, _, .cup _ => emptyIndex
  | _, _, .down _ => unitIndex
  | _, _, .up _ => unitIndex
  | _, _, .comp d e => (Equiv.sumCongr d.hubIndex e.hubIndex).trans (appendIndex d.labels e.labels)
  | _, _, .tensor d e => (Equiv.sumCongr d.hubIndex e.hubIndex).trans (appendIndex d.labels e.labels)

theorem hubLabel_index : {u v : List S} → (d : Diagram P u v) → (h : d.graph.Hub) →
    d.graph.hubLabel h = d.labels[d.hubIndex h]
  | _, _, .identity _, h => h.elim
  | _, _, .cap _, h => h.elim
  | _, _, .cup _, h => h.elim
  | _, _, .down _, _ => rfl
  | _, _, .up _, _ => rfl
  | _, _, .comp d e, h => by
    change d.graph.Hub ⊕ e.graph.Hub at h
    cases h with
    | inl h =>
      change d.graph.hubLabel h = (d.labels ++ e.labels)[appendIndex _ _ (.inl (d.hubIndex h))]
      rw [get_appendIndex]
      exact hubLabel_index d h
    | inr h =>
      change e.graph.hubLabel h = (d.labels ++ e.labels)[appendIndex _ _ (.inr (e.hubIndex h))]
      rw [get_appendIndex]
      exact hubLabel_index e h
  | _, _, .tensor d e, h => by
    change d.graph.Hub ⊕ e.graph.Hub at h
    cases h with
    | inl h =>
      change d.graph.hubLabel h = (d.labels ++ e.labels)[appendIndex _ _ (.inl (d.hubIndex h))]
      rw [get_appendIndex]
      exact hubLabel_index d h
    | inr h =>
      change e.graph.hubLabel h = (d.labels ++ e.labels)[appendIndex _ _ (.inr (e.hubIndex h))]
      rw [get_appendIndex]
      exact hubLabel_index e h

theorem graph_hub_card (d : Diagram P u v) : Fintype.card d.graph.Hub = d.size := by
  calc
    Fintype.card d.graph.Hub = Fintype.card (Fin d.labels.length) := Fintype.card_congr d.hubIndex
    _ = d.size := Fintype.card_fin _

theorem graph_sign (d : Diagram P u v) : d.graph.sign = d.sign := by
  induction d with
  | identity w =>
    change (∑ h : Empty, P.parity h.elim) = 0
    exact Finset.sum_empty
  | cap s =>
    change (∑ h : Empty, P.parity h.elim) = 0
    exact Finset.sum_empty
  | cup s =>
    change (∑ h : Empty, P.parity h.elim) = 0
    exact Finset.sum_empty
  | down r =>
    change (∑ _ : Unit, P.parity r) = ([P.parity r]).sum
    simp
  | up r =>
    change (∑ _ : Unit, P.parity r) = ([P.parity r]).sum
    simp
  | comp d e ihd ihe =>
    change (d.graph.comp e.graph).sign = (d.comp e).sign
    rw [PortGraph.sign_comp, sign_comp, ihd, ihe]
  | tensor d e ihd ihe =>
    change (d.graph.tensor e.graph).sign = (d.tensor e).sign
    rw [PortGraph.sign_tensor, sign_tensor, ihd, ihe]

theorem graph_boundary_eq (d : Diagram P u v) :
    (u.map (InvolutionPresentation.x P)).prod =
      (v.map (InvolutionPresentation.x P)).prod *
        (if d.graph.sign = 1 then InvolutionPresentation.J P else 1) := by
  rw [graph_sign]
  exact d.boundary_eq

end Diagram
end ThomGame.Pictures
