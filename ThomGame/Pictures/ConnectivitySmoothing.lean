module

public import ThomGame.Pictures.GraphBoundaryComponents
public import ThomGame.Pictures.CircuitSmoothing

/-!
# Smoothing preserves actual connectivity between surviving darts

Unlike wire connectivity, this permits turning through relation hubs.
The non-loop case uses the actual bypass; for an isolated loop a
retraction sends its two removed darts to a chosen surviving dart.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv RibbonConnectivity
open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S} (G : PortGraph P u v)

theorem wireConnected_connected {a b : G.Dart} (h : G.WireConnected a b) :
    Connected G.pairing.perm G.circuitStep a b := by
  induction h with
  | refl => exact Connected.refl _
  | @tail b c hab hbc ih =>
    rcases hbc with rfl | rfl
    · exact ih.trans (Connected.edge _)
    · exact ih.trans (G.connected_of_same_vertex (by cases b <;> rfl))

theorem smooth_connected_expands (j : G.Joint) {a b : (G.smooth j).Dart}
    (h : Connected (G.smooth j).pairing.perm (G.smooth j).circuitStep a b) :
    Connected G.pairing.perm G.circuitStep (G.smoothPortEmbedding j a) (G.smoothPortEmbedding j b) := by
  apply h.lift (G.smoothPortEmbedding j) ⟨Connected.refl, Connected.symm, Connected.trans⟩
  · intro x
    exact G.wireConnected_connected (G.smooth_edge_expands j x)
  · intro x
    exact sameCycle_connected _ _ ((G.smooth_sameCycle_iff j x ((G.smooth j).circuitStep x)).mp
      Perm.SameCycle.rfl.apply_right)

theorem bypass_rotation_connected (j : G.Joint)
    (hp : G.pairing.twin (.joint j false) ≠ .joint j true) (x : G.Dart) :
    Connected (G.smooth j).pairing.perm (G.smooth j).circuitStep
      (G.bypass j hp x) (G.bypass j hp (G.rotation x)) := by
  by_cases hxa : x = .joint j false
  · subst x
    exact (G.smooth j).wireConnected_connected (G.bypass_joint j hp)
  by_cases hxb : x = .joint j true
  · subst x
    exact ((G.smooth j).wireConnected_connected (G.bypass_joint j hp)).symm
  let a : (G.smooth j).Dart := (G.smoothPorts j).symm ⟨x, hxa, hxb⟩
  have ha : (G.smoothPorts j a).val = x := congrArg Subtype.val ((G.smoothPorts j).apply_symm_apply _)
  rw [← ha, ← G.smooth_rotation, G.bypass_survivor, G.bypass_survivor]
  exact (G.smooth j).connected_rotation a

theorem bypass_connected (j : G.Joint)
    (hp : G.pairing.twin (.joint j false) ≠ .joint j true) {x y : G.Dart}
    (h : Connected G.pairing.perm G.circuitStep x y) :
    Connected (G.smooth j).pairing.perm (G.smooth j).circuitStep (G.bypass j hp x) (G.bypass j hp y) := by
  apply h.lift (G.bypass j hp) ⟨Connected.refl, Connected.symm, Connected.trans⟩
  · intro x
    exact (G.smooth j).wireConnected_connected (G.bypass_edge j hp x)
  · intro x
    exact ((G.smooth j).wireConnected_connected (G.bypass_edge j hp x)).trans
      (G.bypass_rotation_connected j hp (G.pairing.twin x))

noncomputable def loopRetraction (j : G.Joint) (a : (G.smooth j).Dart) (x : G.Dart) :
    (G.smooth j).Dart :=
  if hx : x ≠ .joint j false ∧ x ≠ .joint j true then
    (G.smoothPorts j).symm ⟨x, hx⟩ else a

theorem loopRetraction_survivor (j : G.Joint) (a x : (G.smooth j).Dart) :
    G.loopRetraction j a (G.smoothPortEmbedding j x) = x := by
  unfold loopRetraction
  split
  · exact (G.smoothPorts j).symm_apply_apply x
  · rename_i hn
    exact (hn (G.smoothPorts j x).property).elim

theorem loopRetraction_left (j : G.Joint) (a : (G.smooth j).Dart) :
    G.loopRetraction j a (.joint j false) = a := by simp [loopRetraction]

theorem loopRetraction_right (j : G.Joint) (a : (G.smooth j).Dart) :
    G.loopRetraction j a (.joint j true) = a := by simp [loopRetraction]

theorem loopRetraction_edge (j : G.Joint)
    (hp : G.pairing.twin (.joint j false) = .joint j true) (a : (G.smooth j).Dart) (x : G.Dart) :
    Connected (G.smooth j).pairing.perm (G.smooth j).circuitStep
      (G.loopRetraction j a x) (G.loopRetraction j a (G.pairing.twin x)) := by
  by_cases hxa : x = .joint j false
  · subst x
    rw [hp, loopRetraction_left, loopRetraction_right]
    exact Connected.refl _
  by_cases hxb : x = .joint j true
  · subst x
    have hp' : G.pairing.twin (.joint j true) = .joint j false := by
      rw [← hp, G.pairing.involutive]
    rw [hp', loopRetraction_left, loopRetraction_right]
    exact Connected.refl _
  let b : (G.smooth j).Dart := (G.smoothPorts j).symm ⟨x, hxa, hxb⟩
  have hb : G.smoothPortEmbedding j b = x := congrArg Subtype.val ((G.smoothPorts j).apply_symm_apply _)
  have he : G.smoothPortEmbedding j ((G.smooth j).pairing.twin b) = G.pairing.twin x := by
    rw [smoothPortEmbedding, Function.Embedding.coeFn_mk, G.smooth_twin_val,
      G.pairing.splice_twin_of_paired (a := .joint j false) (b := .joint j true) rfl hp]
    exact congrArg G.pairing.twin hb
  rw [← he, ← hb, loopRetraction_survivor, loopRetraction_survivor]
  exact Connected.edge _

theorem loopRetraction_rotation (j : G.Joint) (a : (G.smooth j).Dart) (x : G.Dart) :
    Connected (G.smooth j).pairing.perm (G.smooth j).circuitStep
      (G.loopRetraction j a x) (G.loopRetraction j a (G.rotation x)) := by
  by_cases hxa : x = .joint j false
  · subst x
    change Connected _ _ (G.loopRetraction j a (.joint j false)) (G.loopRetraction j a (.joint j true))
    rw [loopRetraction_left, loopRetraction_right]
    exact Connected.refl _
  by_cases hxb : x = .joint j true
  · subst x
    change Connected _ _ (G.loopRetraction j a (.joint j true)) (G.loopRetraction j a (.joint j false))
    rw [loopRetraction_left, loopRetraction_right]
    exact Connected.refl _
  let b : (G.smooth j).Dart := (G.smoothPorts j).symm ⟨x, hxa, hxb⟩
  have hb : (G.smoothPorts j b).val = x := congrArg Subtype.val ((G.smoothPorts j).apply_symm_apply _)
  rw [← hb, ← G.smooth_rotation]
  change Connected _ _ (G.loopRetraction j a (G.smoothPortEmbedding j b))
    (G.loopRetraction j a (G.smoothPortEmbedding j ((G.smooth j).rotation b)))
  rw [loopRetraction_survivor, loopRetraction_survivor]
  exact (G.smooth j).connected_rotation _

theorem loopRetraction_connected (j : G.Joint)
    (hp : G.pairing.twin (.joint j false) = .joint j true) (a : (G.smooth j).Dart) {x y : G.Dart}
    (h : Connected G.pairing.perm G.circuitStep x y) :
    Connected (G.smooth j).pairing.perm (G.smooth j).circuitStep
      (G.loopRetraction j a x) (G.loopRetraction j a y) := by
  apply h.lift (G.loopRetraction j a) ⟨Connected.refl, Connected.symm, Connected.trans⟩
  · exact G.loopRetraction_edge j hp a
  · intro x
    exact (G.loopRetraction_edge j hp a x).trans (G.loopRetraction_rotation j a (G.pairing.twin x))

theorem smooth_connected_iff (j : G.Joint) (a b : (G.smooth j).Dart) :
    Connected (G.smooth j).pairing.perm (G.smooth j).circuitStep a b ↔
      Connected G.pairing.perm G.circuitStep (G.smoothPortEmbedding j a) (G.smoothPortEmbedding j b) := by
  constructor
  · exact G.smooth_connected_expands j
  · intro h
    by_cases hp : G.pairing.twin (.joint j false) = .joint j true
    · have hh := G.loopRetraction_connected j hp a h
      simpa only [G.loopRetraction_survivor] using hh
    · have hh := G.bypass_connected j hp h
      simpa only [smoothPortEmbedding, Function.Embedding.coeFn_mk, G.bypass_survivor] using hh

end ThomGame.Pictures.PortGraph
