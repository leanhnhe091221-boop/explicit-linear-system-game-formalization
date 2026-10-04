module

public import ThomGame.Pictures.SimpleCircuitCut

/-!
# Two combinatorial sides of a simple circuit

The marked cut ports lie in at most two components. Rejoining one pair
of opposite marked ports restores exactly the original connectivity.
Together with the Euler count, this proves that cutting a simple circuit
in an Euler-saturating graph splits exactly its original component into
two. These are components of the cut dual graph; no geometric disk
realization or ordered region diagram is asserted here.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open Equiv FiniteReturn MarkedReturn RibbonConnectivity CycleSurgery
open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  {G : PortGraph P u v} (C : G.SimpleCircuit)

theorem twisted_rotation_marked_sameCycle (x y : Fin C.length × Bool) :
    (C.edgeTwist * G.rotation).SameCycle (C.port x) (C.port y) ↔ x.2 = y.2 := by
  have ht := sameCycle_congr (CircuitPermutations.sides C.length)
    (perm (C.edgeTwist * G.rotation) C.Marked) C.portEquiv C.twisted_rotation_return_port x y
  rw [sameCycle_iff] at ht
  exact ht.symm.trans (CircuitPermutations.sides_sameCycle C.length x y)

theorem cut_marked_connected_of_side (x y : Fin C.length × Bool) (h : x.2 = y.2) :
    Connected G.circuitStep C.cutPairing (C.port x) (C.port y) := by
  have hs : (CircuitPermutations.edge C.length x).2 = (CircuitPermutations.edge C.length y).2 := by
    rw [CircuitPermutations.edge_snd, CircuitPermutations.edge_snd, h]
  have hc := (C.twisted_rotation_marked_sameCycle _ _).mpr hs
  have ht := (sameCycle_congr (C.edgeTwist * G.rotation) (C.cutPairing * G.circuitStep)
    G.pairing.perm C.cutFace_conjugate _ _).mp hc
  change (C.cutPairing * G.circuitStep).SameCycle
    (G.pairing.twin (C.port (CircuitPermutations.edge C.length x)))
    (G.pairing.twin (C.port (CircuitPermutations.edge C.length y))) at ht
  rw [C.twin_port, C.twin_port, CircuitPermutations.edge_involutive,
    CircuitPermutations.edge_involutive] at ht
  exact RotationEuler.sameCycle_mul_connected G.circuitStep C.cutPairing ht

def cutBase : G.Dart := C.port (0, false)

theorem cutBase_marked : C.Marked C.cutBase := ⟨(0, false), rfl⟩

theorem cutMate_marked : C.Marked (G.pairing.twin C.cutBase) :=
  (C.marked_twin_iff _).mpr C.cutBase_marked

theorem cut_port_false_base (i : Fin C.length) :
    Connected G.circuitStep C.cutPairing (C.port (i, false)) C.cutBase :=
  C.cut_marked_connected_of_side (i, false) (0, false) rfl

theorem cut_port_true_mate (i : Fin C.length) :
    Connected G.circuitStep C.cutPairing (C.port (i, true)) (G.pairing.twin C.cutBase) := by
  change Connected G.circuitStep C.cutPairing (C.port (i, true)) (G.pairing.twin (C.port (0, false)))
  rw [C.twin_port]
  exact C.cut_marked_connected_of_side (i, true) (CircuitPermutations.edge C.length (0, false)) rfl

theorem cut_marked_reaches_seam {a : G.Dart} (ha : C.Marked a) :
    Connected G.circuitStep C.cutPairing a C.cutBase ∨
      Connected G.circuitStep C.cutPairing a (G.pairing.twin C.cutBase) := by
  obtain ⟨⟨i, s⟩, rfl⟩ := ha
  cases s
  · exact Or.inl (C.cut_port_false_base i)
  · exact Or.inr (C.cut_port_true_mate i)

noncomputable def reclosedPairing : Perm G.Dart :=
  splice C.cutPairing C.cutBase (G.pairing.twin C.cutBase)

theorem reclosed_seam :
    Connected G.circuitStep C.reclosedPairing C.cutBase (G.pairing.twin C.cutBase) :=
  seam_of_fixed G.circuitStep C.cutPairing (C.cutPairing_of_marked C.cutBase_marked)

theorem reclosed_connected_of_cut {a b : G.Dart}
    (h : Connected G.circuitStep C.cutPairing a b) : Connected G.circuitStep C.reclosedPairing a b :=
  old_connected_of_seam G.circuitStep C.cutPairing C.reclosed_seam h

theorem reclosed_marked {a : G.Dart} (ha : C.Marked a) :
    Connected G.circuitStep C.reclosedPairing a C.cutBase := by
  rcases C.cut_marked_reaches_seam ha with h | h
  · exact C.reclosed_connected_of_cut h
  · exact (C.reclosed_connected_of_cut h).trans C.reclosed_seam.symm

theorem cut_connected_old {a b : G.Dart} (h : Connected G.circuitStep C.cutPairing a b) :
    Connected G.circuitStep G.pairing.perm a b := by
  apply h.lift id ⟨Connected.refl, Connected.symm, Connected.trans⟩ Connected.edge
  intro x
  change Connected G.circuitStep G.pairing.perm x (C.cutPairing x)
  by_cases hx : C.Marked x
  · rw [C.cutPairing_of_marked hx]
    exact Connected.refl _
  · rw [C.cutPairing_of_unmarked _ hx]
    exact Connected.circuit _

theorem old_connected_reclosed {a b : G.Dart} (h : Connected G.circuitStep G.pairing.perm a b) :
    Connected G.circuitStep C.reclosedPairing a b := by
  apply h.lift id ⟨Connected.refl, Connected.symm, Connected.trans⟩ Connected.edge
  intro x
  change Connected G.circuitStep C.reclosedPairing x (G.pairing.twin x)
  by_cases hx : C.Marked x
  · exact (C.reclosed_marked hx).trans (C.reclosed_marked ((C.marked_twin_iff x).mpr hx)).symm
  · have hc : Connected G.circuitStep C.cutPairing x (C.cutPairing x) := Connected.circuit _
    rw [C.cutPairing_of_unmarked _ hx] at hc
    exact C.reclosed_connected_of_cut hc

theorem reclosed_connected_iff (a b : G.Dart) :
    Connected G.circuitStep C.reclosedPairing a b ↔ Connected G.circuitStep G.pairing.perm a b := by
  constructor
  · intro h
    rcases (connected_splice_iff_of_seam G.circuitStep C.cutPairing C.reclosed_seam a b).mp h with
      h | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact C.cut_connected_old h
    · exact (C.cut_connected_old ha).trans ((Connected.circuit C.cutBase).trans (C.cut_connected_old hb).symm)
    · exact (C.cut_connected_old ha).trans ((Connected.circuit C.cutBase).symm.trans (C.cut_connected_old hb).symm)
  · exact C.old_connected_reclosed

theorem reclosed_component_card :
    Nat.card (Component G.circuitStep C.reclosedPairing) =
      Nat.card (Component G.circuitStep G.pairing.perm) :=
  Nat.card_congr (componentEquiv G.circuitStep C.reclosedPairing G.circuitStep G.pairing.perm
    C.reclosed_connected_iff)

theorem cut_component_card_cases :
    Nat.card (Component G.circuitStep C.cutPairing) = Nat.card (Component G.circuitStep G.pairing.perm) ∨
      Nat.card (Component G.circuitStep C.cutPairing) = Nat.card (Component G.circuitStep G.pairing.perm) + 1 := by
  have hr := C.reclosed_component_card
  by_cases h : Connected G.circuitStep C.cutPairing C.cutBase (G.pairing.twin C.cutBase)
  · have hc := component_card_same_of_fixed G.circuitStep C.cutPairing
      (C.cutPairing_of_marked C.cutBase_marked) h
    change Nat.card (Component G.circuitStep C.reclosedPairing) = _ at hc
    exact Or.inl (hc.symm.trans hr)
  · have hc := component_card_join_of_fixed G.circuitStep C.cutPairing
      (C.cutPairing_of_marked C.cutBase_marked) h
    change Nat.card (Component G.circuitStep C.reclosedPairing) + 1 = _ at hc
    rw [hr] at hc
    exact Or.inr hc.symm

/-- An Euler-saturating graph gains exactly one dual component. -/
theorem cut_component_card
    (h : RotationEuler.count G.circuitStep G.pairing.perm =
      2 * Nat.card (Component G.circuitStep G.pairing.perm)) :
    Nat.card (Component G.circuitStep C.cutPairing) =
      Nat.card (Component G.circuitStep G.pairing.perm) + 1 := by
  have hl := C.cut_components_increase h
  rcases C.cut_component_card_cases with he | he
  · omega
  · exact he

theorem cut_sides_separate
    (h : RotationEuler.count G.circuitStep G.pairing.perm =
      2 * Nat.card (Component G.circuitStep G.pairing.perm)) :
    ¬ Connected G.circuitStep C.cutPairing C.cutBase (G.pairing.twin C.cutBase) := by
  intro hc
  have he := component_card_same_of_fixed G.circuitStep C.cutPairing
    (C.cutPairing_of_marked C.cutBase_marked) hc
  change Nat.card (Component G.circuitStep C.reclosedPairing) = _ at he
  rw [C.reclosed_component_card, C.cut_component_card h] at he
  omega

theorem old_connected_base_iff (a : G.Dart) :
    Connected G.circuitStep G.pairing.perm a C.cutBase ↔
      Connected G.circuitStep C.cutPairing a C.cutBase ∨
        Connected G.circuitStep C.cutPairing a (G.pairing.twin C.cutBase) := by
  constructor
  · intro h
    rcases (connected_splice_iff_of_seam G.circuitStep C.cutPairing C.reclosed_seam a C.cutBase).mp
      (C.old_connected_reclosed h) with hc | ⟨ha, _⟩ | ⟨ha, _⟩
    · exact Or.inl hc
    · exact Or.inl ha
    · exact Or.inr ha
  · rintro (h | h)
    · exact C.cut_connected_old h
    · exact (C.cut_connected_old h).trans (Connected.circuit C.cutBase).symm

/-- Outside the original component of the circuit, connectivity is unchanged. -/
theorem cut_connected_iff_outside {a : G.Dart}
    (ha : ¬ Connected G.circuitStep G.pairing.perm a C.cutBase) (b : G.Dart) :
    Connected G.circuitStep C.cutPairing a b ↔ Connected G.circuitStep G.pairing.perm a b := by
  constructor
  · exact C.cut_connected_old
  · intro h
    rcases (connected_splice_iff_of_seam G.circuitStep C.cutPairing C.reclosed_seam a b).mp
      (C.old_connected_reclosed h) with hc | ⟨hx, _⟩ | ⟨hx, _⟩
    · exact hc
    · exact (ha (C.cut_connected_old hx)).elim
    · exact (ha ((C.cut_connected_old hx).trans (Connected.circuit C.cutBase).symm)).elim

theorem cut_marked_connected_iff
    (h : RotationEuler.count G.circuitStep G.pairing.perm =
      2 * Nat.card (Component G.circuitStep G.pairing.perm)) (x y : Fin C.length × Bool) :
    Connected G.circuitStep C.cutPairing (C.port x) (C.port y) ↔ x.2 = y.2 := by
  constructor
  · rcases x with ⟨i, s⟩
    rcases y with ⟨j, t⟩
    intro hc
    cases s <;> cases t
    · rfl
    · exact (C.cut_sides_separate h ((C.cut_port_false_base i).symm.trans
        (hc.trans (C.cut_port_true_mate j)))).elim
    · exact (C.cut_sides_separate h ((C.cut_port_false_base j).symm.trans
        (hc.symm.trans (C.cut_port_true_mate i)))).elim
    · rfl
  · exact C.cut_marked_connected_of_side x y

/-- Forgetting the cut maps every new component into its original one. -/
noncomputable def cutComponentToOld : Component G.circuitStep C.cutPairing →
    Component G.circuitStep G.pairing.perm :=
  Quotient.lift (component G.circuitStep G.pairing.perm)
    (fun _ _ h => (component_eq_iff _ _ _ _).mpr (C.cut_connected_old h))

noncomputable def sideComponent : Bool → Component G.circuitStep C.cutPairing
  | false => component G.circuitStep C.cutPairing C.cutBase
  | true => component G.circuitStep C.cutPairing (G.pairing.twin C.cutBase)

theorem sideComponent_old (s : Bool) :
    C.cutComponentToOld (C.sideComponent s) = component G.circuitStep G.pairing.perm C.cutBase := by
  cases s
  · rfl
  · exact component_circuit G.circuitStep G.pairing.perm C.cutBase

theorem sideComponent_injective
    (h : RotationEuler.count G.circuitStep G.pairing.perm =
      2 * Nat.card (Component G.circuitStep G.pairing.perm)) : Function.Injective C.sideComponent := by
  intro s t he
  cases s <;> cases t
  · rfl
  · exact (C.cut_sides_separate h ((component_eq_iff _ _ _ _).mp he)).elim
  · exact (C.cut_sides_separate h ((component_eq_iff _ _ _ _).mp he.symm)).elim
  · rfl

theorem sideComponent_range (c : Component G.circuitStep C.cutPairing) :
    (∃ s, C.sideComponent s = c) ↔
      C.cutComponentToOld c = component G.circuitStep G.pairing.perm C.cutBase := by
  constructor
  · rintro ⟨s, rfl⟩
    exact C.sideComponent_old s
  · refine Quotient.inductionOn c fun a he => ?_
    have hc := (C.old_connected_base_iff a).mp ((component_eq_iff _ _ _ _).mp he)
    rcases hc with hb | hm
    · exact ⟨false, (component_eq_iff _ _ _ _).mpr hb.symm⟩
    · exact ⟨true, (component_eq_iff _ _ _ _).mpr hm.symm⟩

/-- Exactly two new components lie over the original circuit component. -/
noncomputable def cutSidesEquiv
    (h : RotationEuler.count G.circuitStep G.pairing.perm =
      2 * Nat.card (Component G.circuitStep G.pairing.perm)) :
    Bool ≃ {c : Component G.circuitStep C.cutPairing //
      C.cutComponentToOld c = component G.circuitStep G.pairing.perm C.cutBase} :=
  Equiv.ofBijective (fun s => ⟨C.sideComponent s, C.sideComponent_old s⟩)
    ⟨fun _ _ he => C.sideComponent_injective h (congrArg Subtype.val he), by
      rintro ⟨c, hc⟩
      obtain ⟨s, hs⟩ := (C.sideComponent_range c).mpr hc
      exact ⟨s, Subtype.ext hs⟩⟩

end ThomGame.Pictures.PortGraph.SimpleCircuit
