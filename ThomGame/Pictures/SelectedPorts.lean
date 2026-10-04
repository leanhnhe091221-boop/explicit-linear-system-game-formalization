module

public import ThomGame.Pictures.PortGraph

/-! # Port equivalences for complete selected vertices and one boundary -/

@[expose] public section
namespace ThomGame.Pictures

variable {R S : Type*} {P : InvolutionPresentation R S}

namespace Port

def bottomPorts (w : List S) (H J : Type) (hubLabel : H → R) :
    Port P [] w H J hubLabel ≃ Fin w.length ⊕ Port P [] [] H J hubLabel where
  toFun
    | .top i => i.elim0
    | .bottom i => .inl i
    | .hub h i => .inr (.hub h i)
    | .joint j b => .inr (.joint j b)
  invFun
    | .inl i => .bottom i
    | .inr (.top i) => i.elim0
    | .inr (.bottom i) => i.elim0
    | .inr (.hub h i) => .hub h i
    | .inr (.joint j b) => .joint j b
  left_inv a := by
    cases a with
    | top i => exact i.elim0
    | bottom i => rfl
    | hub h i => rfl
    | joint j b => rfl
  right_inv a := by
    rcases a with i | a
    · rfl
    · cases a with
      | top i => exact i.elim0
      | bottom i => exact i.elim0
      | hub h i => rfl
      | joint j b => rfl

end Port

namespace PortGraph

variable (G : PortGraph P [] []) (V : G.Vertex → Prop)

abbrev SelectedHub := {h : G.Hub // V (.inr (.inl h))}
abbrev SelectedJoint := {j : G.Joint // V (.inr (.inr j))}
abbrev SelectedPort := Port P [] [] (G.SelectedHub V) (G.SelectedJoint V) (fun h => G.hubLabel h.val)

def selectedPorts : G.SelectedPort V ≃ {a : G.Dart // V a.vertex} where
  toFun
    | .top i => i.elim0
    | .bottom i => i.elim0
    | .hub h i => ⟨.hub h.val i, h.property⟩
    | .joint j b => ⟨.joint j.val b, j.property⟩
  invFun
    | ⟨.top i, _⟩ => i.elim0
    | ⟨.bottom i, _⟩ => i.elim0
    | ⟨.hub h i, hh⟩ => .hub ⟨h, hh⟩ i
    | ⟨.joint j b, hj⟩ => .joint ⟨j, hj⟩ b
  left_inv a := by
    cases a with
    | top i => exact i.elim0
    | bottom i => exact i.elim0
    | hub h i => rfl
    | joint j b => rfl
  right_inv a := by
    rcases a with ⟨a, ha⟩
    cases a with
    | top i => exact i.elim0
    | bottom i => exact i.elim0
    | hub h i => rfl
    | joint j b => rfl

theorem selectedPorts_label (a : G.SelectedPort V) :
    Port.label G.jointLabel (G.selectedPorts V a).val =
      Port.label (fun j : G.SelectedJoint V => G.jointLabel j.val) a := by
  cases a with
  | top i => exact i.elim0
  | bottom i => exact i.elim0
  | hub h i => rfl
  | joint j b => rfl

end PortGraph

namespace Pairing

variable {A : Type*} (label : A → S)

/-- Pair two copies of each labelled object. -/
def copies : Pairing (fun a : A × Bool => label a.1) where
  twin a := (a.1, !a.2)
  involutive a := by simp
  ne_self a h := (Bool.not_eq_self a.2).mp (congrArg Prod.snd h)
  label_twin _ := rfl

end Pairing
end ThomGame.Pictures
