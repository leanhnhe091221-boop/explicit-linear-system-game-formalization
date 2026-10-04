module

public import ThomGame.Pictures.PortGraph
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Horizontal and vertical composition of finite port graphs

Vertical composition makes the two matching boundary ports incident at one
new degree-two vertex. Edge pairings are transported from a disjoint union;
there is no quotient of the darts and no unproved gluing assumption.
-/

@[expose] public section
namespace ThomGame.Pictures

variable {R S : Type*} {P : InvolutionPresentation R S}

/-- Positions in a concatenated boundary, preserving repeated labels. -/
def appendIndex (u v : List S) : Fin u.length ⊕ Fin v.length ≃ Fin (u ++ v).length :=
  finSumFinEquiv.trans (finCongr (List.length_append (as := u) (bs := v)).symm)

theorem get_appendIndex (u v : List S) (i : Fin u.length ⊕ Fin v.length) :
    (u ++ v)[appendIndex u v i] = Sum.elim (fun k : Fin u.length => u[k])
      (fun k : Fin v.length => v[k]) i := by
  cases i with
  | inl i => simp [appendIndex, List.getElem_append_left, i.isLt]
  | inr i => simp [appendIndex, List.getElem_append_right]

namespace PortGraph

variable {u v w z : List S}

def compPorts (G : PortGraph P u v) (H : PortGraph P v w) :
    G.Dart ⊕ H.Dart ≃
      Port P u w (G.Hub ⊕ H.Hub) ((G.Joint ⊕ H.Joint) ⊕ Fin v.length)
        (Sum.elim G.hubLabel H.hubLabel) where
  toFun
    | .inl (.top i) => .top i
    | .inl (.bottom i) => .joint (.inr i) false
    | .inl (.hub h i) => .hub (.inl h) i
    | .inl (.joint j side) => .joint (.inl (.inl j)) side
    | .inr (.top i) => .joint (.inr i) true
    | .inr (.bottom i) => .bottom i
    | .inr (.hub h i) => .hub (.inr h) i
    | .inr (.joint j side) => .joint (.inl (.inr j)) side
  invFun
    | .top i => .inl (.top i)
    | .bottom i => .inr (.bottom i)
    | .hub (.inl h) i => .inl (.hub h i)
    | .hub (.inr h) i => .inr (.hub h i)
    | .joint (.inl (.inl j)) side => .inl (.joint j side)
    | .joint (.inl (.inr j)) side => .inr (.joint j side)
    | .joint (.inr i) false => .inl (.bottom i)
    | .joint (.inr i) true => .inr (.top i)
  left_inv a := by rcases a with a | a <;> cases a <;> rfl
  right_inv a := by
    cases a with
    | top i => rfl
    | bottom i => rfl
    | hub h i => cases h <;> rfl
    | joint j side => rcases j with (j | j) | i <;> cases side <;> rfl

def comp (G : PortGraph P u v) (H : PortGraph P v w) : PortGraph P u w where
  Hub := G.Hub ⊕ H.Hub
  Joint := (G.Joint ⊕ H.Joint) ⊕ Fin v.length
  hubLabel := Sum.elim G.hubLabel H.hubLabel
  hubFlip := Sum.elim G.hubFlip H.hubFlip
  jointLabel := Sum.elim (Sum.elim G.jointLabel H.jointLabel) (fun i => v[i])
  pairing := (G.pairing.sum H.pairing).transport (compPorts G H) _ (by
    intro a
    rcases a with a | a <;> cases a <;> rfl)

theorem comp_hub_card (G : PortGraph P u v) (H : PortGraph P v w) :
    Fintype.card (G.comp H).Hub = Fintype.card G.Hub + Fintype.card H.Hub :=
  Fintype.card_sum

theorem comp_joint_card (G : PortGraph P u v) (H : PortGraph P v w) :
    Fintype.card (G.comp H).Joint =
      Fintype.card G.Joint + Fintype.card H.Joint + v.length := by
  change Fintype.card ((G.Joint ⊕ H.Joint) ⊕ Fin v.length) = _
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_fin]

/-- Vertical composition leaves every edge pairing in its original summand. -/
theorem twin_compPorts (G : PortGraph P u v) (H : PortGraph P v w) (a : G.Dart ⊕ H.Dart) :
    (G.comp H).pairing.twin (compPorts G H a) =
      compPorts G H (Sum.map G.pairing.twin H.pairing.twin a) := by
  simp only [comp, Pairing.transport, Equiv.symm_apply_apply, Pairing.sum]

def tensorPorts (G : PortGraph P u v) (H : PortGraph P w z) :
    G.Dart ⊕ H.Dart ≃
      Port P (u ++ w) (v ++ z) (G.Hub ⊕ H.Hub) (G.Joint ⊕ H.Joint)
        (Sum.elim G.hubLabel H.hubLabel) where
  toFun
    | .inl (.top i) => .top (appendIndex u w (.inl i))
    | .inl (.bottom i) => .bottom (appendIndex v z (.inl i))
    | .inl (.hub h i) => .hub (.inl h) i
    | .inl (.joint j side) => .joint (.inl j) side
    | .inr (.top i) => .top (appendIndex u w (.inr i))
    | .inr (.bottom i) => .bottom (appendIndex v z (.inr i))
    | .inr (.hub h i) => .hub (.inr h) i
    | .inr (.joint j side) => .joint (.inr j) side
  invFun
    | .top i => Sum.elim (fun k => .inl (.top k)) (fun k => .inr (.top k))
        ((appendIndex u w).symm i)
    | .bottom i => Sum.elim (fun k => .inl (.bottom k)) (fun k => .inr (.bottom k))
        ((appendIndex v z).symm i)
    | .hub (.inl h) i => .inl (.hub h i)
    | .hub (.inr h) i => .inr (.hub h i)
    | .joint (.inl j) side => .inl (.joint j side)
    | .joint (.inr j) side => .inr (.joint j side)
  left_inv a := by rcases a with a | a <;> cases a <;> simp
  right_inv a := by
    cases a with
    | top i =>
      obtain ⟨k, rfl⟩ := (appendIndex u w).surjective i
      cases k <;> simp
    | bottom i =>
      obtain ⟨k, rfl⟩ := (appendIndex v z).surjective i
      cases k <;> simp
    | hub h i => cases h <;> rfl
    | joint j side => cases j <;> rfl

def tensor (G : PortGraph P u v) (H : PortGraph P w z) : PortGraph P (u ++ w) (v ++ z) where
  Hub := G.Hub ⊕ H.Hub
  Joint := G.Joint ⊕ H.Joint
  hubLabel := Sum.elim G.hubLabel H.hubLabel
  hubFlip := Sum.elim G.hubFlip H.hubFlip
  jointLabel := Sum.elim G.jointLabel H.jointLabel
  pairing := (G.pairing.sum H.pairing).transport (tensorPorts G H) _ (by
    intro a
    rcases a with a | a <;> cases a <;>
      simp only [tensorPorts, Equiv.coe_fn_mk, Port.label, get_appendIndex, Sum.elim_inl,
        Sum.elim_inr])

theorem tensor_hub_card (G : PortGraph P u v) (H : PortGraph P w z) :
    Fintype.card (G.tensor H).Hub = Fintype.card G.Hub + Fintype.card H.Hub :=
  Fintype.card_sum

theorem tensor_joint_card (G : PortGraph P u v) (H : PortGraph P w z) :
    Fintype.card (G.tensor H).Joint = Fintype.card G.Joint + Fintype.card H.Joint :=
  Fintype.card_sum

theorem twin_tensorPorts (G : PortGraph P u v) (H : PortGraph P w z) (a : G.Dart ⊕ H.Dart) :
    (G.tensor H).pairing.twin (tensorPorts G H a) =
      tensorPorts G H (Sum.map G.pairing.twin H.pairing.twin a) := by
  simp only [tensor, Pairing.transport, Equiv.symm_apply_apply, Pairing.sum]

end PortGraph
end ThomGame.Pictures
