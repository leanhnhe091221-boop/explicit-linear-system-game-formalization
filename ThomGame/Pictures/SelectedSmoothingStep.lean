module

public import ThomGame.Pictures.SmoothedWires
public import ThomGame.Pictures.ReturnPaths

/-!
# Smoothing only selected junctions

The selected turn flips only junctions scheduled for removal. All other
ports, including the ports of retained junctions, are terminals. Removing
one selected junction advances its edge-and-turn permutation by one or
two genuine steps and preserves the exact return to these terminals.
-/

@[expose] public section
namespace ThomGame.Pictures

theorem MarkedReturn.Hit.sameCycle {A : Type*} {f : Equiv.Perm A} {p : A → Prop}
    {x y : A} (h : MarkedReturn.Hit f p x y) : f.SameCycle x y := by
  induction h with
  | direct x => exact ⟨1, by simp⟩
  | skip x _ _ ih => exact (show f.SameCycle x (f x) from ⟨1, by simp⟩).trans ih

namespace PortGraph

open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S} (G : PortGraph P u v)

def SelectedTerminal (remove : G.Joint → Prop) : G.Dart → Prop
  | .joint j _ => ¬ remove j
  | _ => True

noncomputable def selectedTurn (remove : G.Joint → Prop) : G.Dart → G.Dart
  | .joint j b => if remove j then .joint j (!b) else .joint j b
  | a => a

theorem selectedTurn_involutive (remove : G.Joint → Prop) : Function.Involutive (G.selectedTurn remove) := by
  intro a
  cases a with
  | top i => rfl
  | bottom i => rfl
  | hub h i => rfl
  | joint j b => by_cases hj : remove j <;> simp [selectedTurn, hj]

noncomputable def selectedTurnPerm (remove : G.Joint → Prop) : Equiv.Perm G.Dart :=
  ⟨G.selectedTurn remove, G.selectedTurn remove, G.selectedTurn_involutive remove,
    G.selectedTurn_involutive remove⟩

noncomputable def selectedStep (remove : G.Joint → Prop) : Equiv.Perm G.Dart :=
  G.selectedTurnPerm remove * G.pairing.perm

theorem selectedStep_apply (remove : G.Joint → Prop) (a : G.Dart) :
    G.selectedStep remove a = G.selectedTurn remove (G.pairing.twin a) := rfl

theorem selectedTurn_eq_self (remove : G.Joint → Prop) (a : G.Dart) (ha : G.SelectedTerminal remove a) :
    G.selectedTurn remove a = a := by
  cases a with
  | top i => rfl
  | bottom i => rfl
  | hub h i => rfl
  | joint j b => exact ite_eq_right ha

theorem smooth_selectedTurn (remove : G.Joint → Prop) (j : G.Joint) (a : (G.smooth j).Dart) :
    G.smoothPortEmbedding j ((G.smooth j).selectedTurn (fun k => remove k.val) a) =
      G.selectedTurn remove (G.smoothPortEmbedding j a) := by
  cases a with
  | top i => rfl
  | bottom i => rfl
  | hub h i => rfl
  | joint k b => by_cases hk : remove k.val <;> simp [selectedTurn, hk, smoothPortEmbedding, smoothPorts]

theorem smooth_selectedTerminal_iff (remove : G.Joint → Prop) (j : G.Joint) (a : (G.smooth j).Dart) :
    G.SelectedTerminal remove (G.smoothPortEmbedding j a) ↔
      (G.smooth j).SelectedTerminal (fun k => remove k.val) a := by cases a <;> rfl

theorem selectedTerminal_survives (remove : G.Joint → Prop) (j : G.Joint) (hj : remove j)
    (a : G.Dart) (ha : G.SelectedTerminal remove a) :
    ∃ b : (G.smooth j).Dart, (G.smooth j).SelectedTerminal (fun k => remove k.val) b ∧
      G.smoothPortEmbedding j b = a := by
  cases a with
  | top i => exact ⟨.top i, trivial, rfl⟩
  | bottom i => exact ⟨.bottom i, trivial, rfl⟩
  | hub h i => exact ⟨.hub h i, trivial, rfl⟩
  | joint k b =>
    have hkj : k ≠ j := fun he => ha (he ▸ hj)
    exact ⟨.joint ⟨k, hkj⟩ b, ha, rfl⟩

theorem smooth_selectedStep_val (remove : G.Joint → Prop) (j : G.Joint) (a : (G.smooth j).Dart) :
    G.smoothPortEmbedding j ((G.smooth j).selectedStep (fun k => remove k.val) a) =
      G.selectedTurn remove ((G.pairing.splice (.joint j false) (.joint j true) rfl).twin
        (G.smoothPortEmbedding j a)) := by
  rw [(G.smooth j).selectedStep_apply, G.smooth_selectedTurn]
  exact congrArg (G.selectedTurn remove) (G.smooth_twin_val j a)

theorem smooth_selected_advances (remove : G.Joint → Prop) (j : G.Joint) (hj : remove j) :
    FiniteReturn.Advances (G.selectedStep remove)
      ((G.smooth j).selectedStep (fun k => remove k.val)) (G.smoothPortEmbedding j) := by
  intro x
  let a : G.Dart := .joint j false
  let b : G.Dart := .joint j true
  have hab : a ≠ b := by simp [a, b]
  have hl : Port.label G.jointLabel a = Port.label G.jointLabel b := rfl
  by_cases hxa : G.smoothPortEmbedding j x = G.pairing.twin a
  · have hn : G.selectedStep remove (G.smoothPortEmbedding j x) = b := by
      rw [hxa, G.selectedStep_apply, G.pairing.involutive]
      exact ite_eq_left hj
    refine Or.inr ⟨?_, ?_⟩
    · rw [hn, G.smooth_selectedStep_val, hxa, G.pairing.splice_twin_partner_left hab hl]
      rfl
    · intro y hy
      rw [hn] at hy
      exact (G.smoothPorts j y).property.2 hy
  by_cases hxb : G.smoothPortEmbedding j x = G.pairing.twin b
  · have hn : G.selectedStep remove (G.smoothPortEmbedding j x) = a := by
      rw [hxb, G.selectedStep_apply, G.pairing.involutive]
      exact ite_eq_left hj
    refine Or.inr ⟨?_, ?_⟩
    · rw [hn, G.smooth_selectedStep_val, hxb, G.pairing.splice_twin_partner_right hab hl]
      rfl
    · intro y hy
      rw [hn] at hy
      exact (G.smoothPorts j y).property.1 hy
  · refine Or.inl ?_
    rw [G.smooth_selectedStep_val]
    exact congrArg (G.selectedTurn remove) (G.pairing.splice_twin_unchanged hl
      (G.smoothPorts j x).property.1 (G.smoothPorts j x).property.2 hxa hxb)

theorem smooth_selected_return (remove : G.Joint → Prop) (j : G.Joint) (hj : remove j)
    (a : {a : (G.smooth j).Dart // (G.smooth j).SelectedTerminal (fun k => remove k.val) a}) :
    G.smoothPortEmbedding j
      (MarkedReturn.perm ((G.smooth j).selectedStep (fun k => remove k.val))
        ((G.smooth j).SelectedTerminal (fun k => remove k.val)) a).val =
      (MarkedReturn.perm (G.selectedStep remove) (G.SelectedTerminal remove)
        ⟨G.smoothPortEmbedding j a.val, (G.smooth_selectedTerminal_iff remove j a.val).mpr a.property⟩).val :=
  MarkedReturn.perm_preserved _ _ _ _ _ (G.smooth_selected_advances remove j hj)
    (G.smooth_selectedTerminal_iff remove j)
    (fun a ha => by obtain ⟨b, _, hb⟩ := G.selectedTerminal_survives remove j hj a ha; exact ⟨b, hb⟩) a

/-- Every selected wire reaches a port which will remain. -/
def SelectedAccessible (remove : G.Joint → Prop) : Prop :=
  ∀ a : G.Dart, ∃ b : G.Dart, G.SelectedTerminal remove b ∧ (G.selectedStep remove).SameCycle a b

theorem selected_not_loop (remove : G.Joint → Prop) (h : G.SelectedAccessible remove)
    (j : G.Joint) (hj : remove j) : G.pairing.twin (.joint j false) ≠ .joint j true := by
  intro hp
  have hf : G.selectedStep remove (.joint j false) = .joint j false := by
    rw [G.selectedStep_apply, hp]
    exact ite_eq_left hj
  obtain ⟨b, hb, hc⟩ := h (.joint j false)
  have he : b = .joint j false := hc.symm.eq_of_right hf
  subst b
  exact hb hj

theorem smooth_selectedAccessible (remove : G.Joint → Prop) (h : G.SelectedAccessible remove)
    (j : G.Joint) (hj : remove j) :
    (G.smooth j).SelectedAccessible (fun k => remove k.val) := by
  intro a
  obtain ⟨b, hb, hc⟩ := h (G.smoothPortEmbedding j a)
  obtain ⟨c, hc', he⟩ := G.selectedTerminal_survives remove j hj b hb
  refine ⟨c, hc', (G.smooth_selected_advances remove j hj).sameCycle_iff _ _ |>.mpr ?_⟩
  rwa [he]

end PortGraph
end ThomGame.Pictures
