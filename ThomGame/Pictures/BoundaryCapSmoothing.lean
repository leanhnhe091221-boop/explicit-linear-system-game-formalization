module

public import ThomGame.Pictures.AdjoinedGraph
public import ThomGame.Pictures.SelectedSmoothingTrace

/-!
# Smoothing the actual auxiliary boundary star

Compose an auxiliary upward relation star with the relabelled graph.
Only the newly created boundary seams are removed. Their selected first
returns reproduce the original pairing exactly, while the auxiliary
star supplies the reversed boundary rotation. Old joints remain intact.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv MarkedReturn
open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {w : List S}
  (G : PortGraph P w [])

@[reducible] def boundaryStar (_G : PortGraph P w []) : PortGraph (P.adjoinRelation w 0) [] w :=
  up (P.adjoinRelation w 0) none

@[reducible] def boundaryClosure : PortGraph (P.adjoinRelation w 0) [] [] :=
  G.boundaryStar.comp (G.adjoinGraph w)

def boundaryClosureRemove : G.boundaryClosure.Joint → Prop
  | .inl _ => False
  | .inr _ => True

def boundaryClosureInput (x : G.Dart) : G.boundaryClosure.Dart :=
  compPorts G.boundaryStar (G.adjoinGraph w) (.inr (G.adjoinPorts w x))

def boundaryClosurePort : G.Dart → G.boundaryClosure.Dart
  | .top i => .hub (.inl ()) i
  | .bottom i => i.elim0
  | .hub h i => .hub (.inr h) i
  | .joint j side => .joint (.inl (.inr j)) side

theorem boundaryClosurePort_terminal (x : G.Dart) :
    G.boundaryClosure.SelectedTerminal G.boundaryClosureRemove (G.boundaryClosurePort x) := by
  cases x with
  | top i => trivial
  | bottom i => exact i.elim0
  | hub h i => trivial
  | joint j side => exact not_false

def boundaryClosurePorts : G.Dart ≃
    {x : G.boundaryClosure.Dart // G.boundaryClosure.SelectedTerminal G.boundaryClosureRemove x} where
  toFun x := ⟨G.boundaryClosurePort x, G.boundaryClosurePort_terminal x⟩
  invFun
    | ⟨.top i, _⟩ => i.elim0
    | ⟨.bottom i, _⟩ => i.elim0
    | ⟨.hub (.inl _) i, _⟩ => .top i
    | ⟨.hub (.inr h) i, _⟩ => .hub h i
    | ⟨.joint (.inl (.inl j)) _, _⟩ => j.elim
    | ⟨.joint (.inl (.inr j)) side, _⟩ => .joint j side
    | ⟨.joint (.inr _) _, hx⟩ => (hx trivial).elim
  left_inv x := by
    cases x with
    | top i => rfl
    | bottom i => exact i.elim0
    | hub h i => rfl
    | joint j side => rfl
  right_inv x := by
    rcases x with ⟨x, hx⟩
    cases x with
    | top i => exact i.elim0
    | bottom i => exact i.elim0
    | hub h i => cases h with
      | inl h => cases h; rfl
      | inr h => rfl
    | joint j side =>
      rcases j with (j | j) | i
      · exact j.elim
      · rfl
      · exact (hx trivial).elim

theorem boundaryClosureInput_twin (x : G.Dart) :
    G.boundaryClosure.pairing.twin (G.boundaryClosureInput x) =
      G.boundaryClosureInput (G.pairing.twin x) := by
  have h := twin_compPorts G.boundaryStar (G.adjoinGraph w) (.inr (G.adjoinPorts w x))
  exact h.trans (congrArg (fun y => compPorts G.boundaryStar (G.adjoinGraph w) (.inr y))
    (G.adjoin_pairing w x))

theorem boundaryClosure_seam_false_step (i : Fin w.length) :
    G.boundaryClosure.selectedStep G.boundaryClosureRemove (.joint (.inr i) false) =
      G.boundaryClosurePort (.top i) := rfl

theorem boundaryClosure_frame_step (i : Fin w.length) :
    G.boundaryClosure.selectedStep G.boundaryClosureRemove (G.boundaryClosurePort (.top i)) =
      G.boundaryClosureInput (.top i) := by
  change G.boundaryClosure.selectedTurn G.boundaryClosureRemove (.joint (.inr i) false) =
    .joint (.inr i) true
  simp [selectedTurn, boundaryClosureRemove]

theorem boundaryClosureInput_hit (x : G.Dart) :
    Hit (G.boundaryClosure.selectedStep G.boundaryClosureRemove)
      (G.boundaryClosure.SelectedTerminal G.boundaryClosureRemove)
      (G.boundaryClosureInput x) (G.boundaryClosurePort (G.pairing.twin x)) := by
  have he : G.boundaryClosure.selectedStep G.boundaryClosureRemove (G.boundaryClosureInput x) =
      G.boundaryClosure.selectedTurn G.boundaryClosureRemove (G.boundaryClosureInput (G.pairing.twin x)) := by
    rw [G.boundaryClosure.selectedStep_apply, G.boundaryClosureInput_twin]
  cases ht : G.pairing.twin x with
  | top i =>
    have hs : G.boundaryClosure.selectedStep G.boundaryClosureRemove (G.boundaryClosureInput x) =
        .joint (.inr i) false := by
      rw [he, ht]
      simp [selectedTurn, boundaryClosureInput, compPorts, adjoinPorts, boundaryClosureRemove]
    apply Hit.skip (G.boundaryClosureInput x)
    · rw [hs]
      exact not_not_intro trivial
    · rw [hs, ← G.boundaryClosure_seam_false_step i]
      exact Hit.direct _
  | bottom i => exact i.elim0
  | hub h i =>
    have hs : G.boundaryClosure.selectedStep G.boundaryClosureRemove (G.boundaryClosureInput x) =
        G.boundaryClosurePort (.hub h i) := by rw [he, ht]; rfl
    rw [← hs]
    exact Hit.direct _
  | joint j side =>
    have hs : G.boundaryClosure.selectedStep G.boundaryClosureRemove (G.boundaryClosureInput x) =
        G.boundaryClosurePort (.joint j side) := by
      rw [he, ht]
      simp [selectedTurn, boundaryClosureInput, compPorts, adjoinPorts, boundaryClosureRemove,
        boundaryClosurePort]
    rw [← hs]
    exact Hit.direct _

theorem boundaryClosurePort_hit (x : G.Dart) :
    Hit (G.boundaryClosure.selectedStep G.boundaryClosureRemove)
      (G.boundaryClosure.SelectedTerminal G.boundaryClosureRemove)
      (G.boundaryClosurePort x) (G.boundaryClosurePort (G.pairing.twin x)) := by
  cases x with
  | top i =>
    apply Hit.skip (G.boundaryClosurePort (.top i))
    · rw [G.boundaryClosure_frame_step]
      exact not_not_intro trivial
    · rw [G.boundaryClosure_frame_step]
      exact G.boundaryClosureInput_hit (.top i)
  | bottom i => exact i.elim0
  | hub h i => exact G.boundaryClosureInput_hit (.hub h i)
  | joint j side => exact G.boundaryClosureInput_hit (.joint j side)

theorem boundaryClosure_selectedAccessible : G.boundaryClosure.SelectedAccessible G.boundaryClosureRemove := by
  intro x
  cases x with
  | top i => exact i.elim0
  | bottom i => exact i.elim0
  | hub h i => exact ⟨.hub h i, trivial, Perm.SameCycle.rfl⟩
  | joint j side =>
    rcases j with (j | j) | i
    · exact j.elim
    · exact ⟨.joint (.inl (.inr j)) side, not_false, Perm.SameCycle.rfl⟩
    · cases side with
      | false =>
        refine ⟨G.boundaryClosurePort (.top i), G.boundaryClosurePort_terminal _, ?_⟩
        rw [← G.boundaryClosure_seam_false_step]
        exact Perm.SameCycle.rfl.apply_right
      | true => exact ⟨G.boundaryClosurePort (G.pairing.twin (.top i)),
          G.boundaryClosurePort_terminal _, (G.boundaryClosureInput_hit (.top i)).sameCycle⟩

theorem boundaryClosure_return (x : G.Dart) :
    (MarkedReturn.perm (G.boundaryClosure.selectedStep G.boundaryClosureRemove)
      (G.boundaryClosure.SelectedTerminal G.boundaryClosureRemove) (G.boundaryClosurePorts x)).val =
        G.boundaryClosurePort (G.pairing.twin x) :=
  (MarkedReturn.eq_perm_of_hit _ _ (G.boundaryClosurePorts x)
    (G.boundaryClosurePort_terminal _) (G.boundaryClosurePort_hit x)).symm

theorem boundaryClosure_rotation (x : G.Dart) :
    G.boundaryClosure.rotation (G.boundaryClosurePort x) = G.boundaryClosurePort (G.cappedRotation x) := by
  cases x with
  | top i => rw [G.cappedRotation_top]; rfl
  | bottom i => exact i.elim0
  | hub h i => rw [G.cappedRotation_hub]; rfl
  | joint j side => rw [G.cappedRotation_joint]; rfl

end ThomGame.Pictures.PortGraph
