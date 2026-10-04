module

public import ThomGame.Pictures.PairingSurgery
public import ThomGame.Pictures.DiagramGraph
public import ThomGame.Pictures.GraphRotation

/-!
# Removing one degree-two junction

The surviving ports, hubs, and boundary positions retain their identities.
The two incident edges are joined by the proved pairing surgery. An isolated
loop is recorded separately; this file makes no planar-region assertion.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S} (G : PortGraph P u v)

abbrev SmoothDart (j : G.Joint) := Port P u v G.Hub {k : G.Joint // k ≠ j} G.hubLabel

theorem joint_ne_of_away {j k : G.Joint} {side : Bool}
    (h : (Port.joint k side : G.Dart) ≠ .joint j false ∧
      (Port.joint k side : G.Dart) ≠ .joint j true) : k ≠ j := by
  intro hkj
  subst k
  cases side with
  | false => exact h.1 rfl
  | true => exact h.2 rfl

def smoothPorts (j : G.Joint) : G.SmoothDart j ≃
    Pairing.Away (Port.joint j false : G.Dart) (.joint j true) where
  toFun
    | .top i => ⟨.top i, by simp⟩
    | .bottom i => ⟨.bottom i, by simp⟩
    | .hub h i => ⟨.hub h i, by simp⟩
    | .joint k side => ⟨.joint k.val side, by simp [k.property]⟩
  invFun
    | ⟨.top i, _⟩ => .top i
    | ⟨.bottom i, _⟩ => .bottom i
    | ⟨.hub h i, _⟩ => .hub h i
    | ⟨.joint k side, h⟩ => .joint ⟨k, G.joint_ne_of_away h⟩ side
  left_inv a := by cases a <;> rfl
  right_inv a := by rcases a with ⟨a, ha⟩; cases a <;> rfl

theorem smoothPorts_label (j : G.Joint) (a : G.SmoothDart j) :
    Port.label G.jointLabel (G.smoothPorts j a).val =
      Port.label (fun k : {k : G.Joint // k ≠ j} => G.jointLabel k.val) a := by
  cases a <;> rfl

@[reducible] noncomputable def smooth (j : G.Joint) : PortGraph P u v where
  Hub := G.Hub
  Joint := {k : G.Joint // k ≠ j}
  hubFintype := G.hubFintype
  hubLabel := G.hubLabel
  hubFlip := G.hubFlip
  jointLabel k := G.jointLabel k.val
  pairing := (G.pairing.smooth (.joint j false) (.joint j true) (by simp) rfl).transport
    (G.smoothPorts j).symm _ (by
      intro a
      obtain ⟨b, rfl⟩ := (G.smoothPorts j).surjective a
      simpa only [Equiv.symm_apply_apply] using (G.smoothPorts_label j b).symm)

theorem smooth_hub_label (j : G.Joint) (h : (G.smooth j).Hub) :
    (G.smooth j).hubLabel h = G.hubLabel h := rfl

theorem smooth_hub_flip (j : G.Joint) (h : (G.smooth j).Hub) :
    (G.smooth j).hubFlip h = G.hubFlip h := rfl

theorem smooth_sign (j : G.Joint) : (G.smooth j).sign = G.sign := rfl

theorem smooth_hub_card (j : G.Joint) : Fintype.card (G.smooth j).Hub = Fintype.card G.Hub := rfl

theorem smooth_joint_card (j : G.Joint) :
    Fintype.card (G.smooth j).Joint + 1 = Fintype.card G.Joint := by
  change Fintype.card {k : G.Joint // k ≠ j} + 1 = _
  have h := Fintype.card_subtype_compl (fun k : G.Joint => k = j)
  rw [Fintype.card_subtype_eq] at h
  rw [h]
  have hp : 0 < Fintype.card G.Joint := Fintype.card_pos_iff.mpr ⟨j⟩
  omega

theorem smooth_joint_card_lt (j : G.Joint) :
    Fintype.card (G.smooth j).Joint < Fintype.card G.Joint := by
  have h := G.smooth_joint_card j
  omega

theorem smooth_twin (j : G.Joint) (a : (G.smooth j).Dart) :
    G.smoothPorts j ((G.smooth j).pairing.twin a) =
      (G.pairing.smooth (.joint j false) (.joint j true) (by simp) rfl).twin (G.smoothPorts j a) := by
  simp only [smooth, Pairing.transport, Equiv.symm_symm, Equiv.apply_symm_apply]

theorem smooth_twin_val (j : G.Joint) (a : (G.smooth j).Dart) :
    (G.smoothPorts j ((G.smooth j).pairing.twin a)).val =
      (G.pairing.splice (.joint j false) (.joint j true) rfl).twin (G.smoothPorts j a).val := by
  rw [G.smooth_twin]
  rfl

/-- A circle with no retained vertices is explicitly recorded when it disappears. -/
noncomputable def smoothCircles (j : G.Joint) : List S :=
  if G.pairing.twin (.joint j false) = .joint j true then [G.jointLabel j] else []

theorem smoothCircles_of_loop (j : G.Joint)
    (h : G.pairing.twin (.joint j false) = .joint j true) :
    G.smoothCircles j = [G.jointLabel j] := by simp [smoothCircles, h]

theorem smoothCircles_of_not_loop (j : G.Joint)
    (h : G.pairing.twin (.joint j false) ≠ .joint j true) :
    G.smoothCircles j = [] := by simp [smoothCircles, h]

theorem smooth_edge_card (j : G.Joint) :
    Fintype.card (G.smooth j).Edge + 1 = Fintype.card G.Edge := by
  have hG := G.degree_sum
  have hH := (G.smooth j).degree_sum
  have hJ := G.smooth_joint_card j
  change u.length + v.length +
    ((∑ h : G.Hub, (P.word (G.hubLabel h)).length) + 2 * Fintype.card (G.smooth j).Joint) =
      2 * Fintype.card (G.smooth j).Edge at hH
  omega

/-- Local cyclic order on every surviving port is unchanged. -/
theorem smooth_rotation (j : G.Joint) (a : (G.smooth j).Dart) :
    (G.smoothPorts j ((G.smooth j).rotation a)).val =
      G.rotation (G.smoothPorts j a).val := by
  cases a <;> rfl

end ThomGame.Pictures.PortGraph
