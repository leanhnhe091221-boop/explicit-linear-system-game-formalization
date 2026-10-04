module

public import ThomGame.Pictures.SimpleCircuitSeparation

/-!
# Vertex sectors along a cut circuit

Away from the circuit, all ports of one vertex remain on one cut side.
At circuit vertices, the two orbits of the twisted vertex rotation
describe the two sectors. For unmarked ports their orbit directions
correspond to the opposite cut-side directions, as forced by edge
reversal in the dual conjugacy.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open Equiv FiniteReturn MarkedReturn RibbonConnectivity
open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  {G : PortGraph P u v} (C : G.SimpleCircuit)

def OnCircuitVertex (x : G.Vertex) : Prop := ∃ i, (C.dart i).vertex = x

def OnSide (s : Bool) (a : G.Dart) : Prop :=
  Connected G.circuitStep C.cutPairing a (C.port (0, s))

def Sector (s : Bool) (a : G.Dart) : Prop :=
  (C.edgeTwist * G.rotation).SameCycle (C.port (0, s)) a

theorem marked_onCircuitVertex {a : G.Dart} (ha : C.Marked a) : C.OnCircuitVertex a.vertex := by
  obtain ⟨x, rfl⟩ := ha
  exact ⟨x.1, (C.port_vertex x).symm⟩

theorem onCircuitVertex_iff_not_avoids (a : G.Dart) :
    C.OnCircuitVertex a.vertex ↔ ¬ Avoids G.rotation C.Marked a := by
  constructor
  · rintro ⟨i, hi⟩ ha
    exact ha (C.dart i) ((G.rotation_sameCycle_iff _ _).mpr hi.symm) ⟨(i, false), rfl⟩
  · intro ha
    by_contra hn
    apply ha
    intro b hb hm
    have hv := (G.rotation_sameCycle_iff _ _).mp hb
    exact hn (hv ▸ C.marked_onCircuitVertex hm)

theorem sector_marked (s : Bool) (x : Fin C.length × Bool) : C.Sector s (C.port x) ↔ s = x.2 :=
  C.twisted_rotation_marked_sameCycle (0, s) x

theorem onCircuitVertex_iff_sector (a : G.Dart) :
    C.OnCircuitVertex a.vertex ↔ ∃ s, C.Sector s a := by
  rw [C.onCircuitVertex_iff_not_avoids,
    ← avoids_mul_iff G.rotation C.Marked C.edgeTwist C.edgeTwist_of_unmarked]
  constructor
  · intro hn
    have he : ∃ b, (C.edgeTwist * G.rotation).SameCycle a b ∧ C.Marked b := by
      by_contra he
      apply hn
      intro b hb hm
      exact he ⟨b, hb, hm⟩
    obtain ⟨b, hb, x, rfl⟩ := he
    exact ⟨x.2, ((C.sector_marked x.2 x).mpr rfl).trans hb.symm⟩
  · rintro ⟨s, hs⟩ hn
    exact hn (C.port (0, s)) hs.symm ⟨(0, s), rfl⟩

theorem sector_unique {a : G.Dart} {s t : Bool} (hs : C.Sector s a) (ht : C.Sector t a) : s = t :=
  (C.sector_marked s (0, t)).mp (hs.trans ht.symm)

theorem cut_connected_rotation_of_unmarked {a : G.Dart} (ha : ¬ C.Marked a) :
    Connected G.circuitStep C.cutPairing a (G.rotation a) := by
  have he : Connected G.circuitStep C.cutPairing a (G.pairing.twin a) := by
    rw [← C.cutPairing_of_unmarked a ha]
    exact Connected.circuit _
  have hr : Connected G.circuitStep C.cutPairing (G.pairing.twin a)
      (G.circuitStep (G.pairing.twin a)) := Connected.edge _
  have hx : G.circuitStep (G.pairing.twin a) = G.rotation a := by
    rw [G.circuitStep_apply, G.pairing.involutive]
  rw [hx] at hr
  exact he.trans hr

theorem cut_connected_same_vertex {a b : G.Dart} (ha : ¬ C.OnCircuitVertex a.vertex)
    (hv : a.vertex = b.vertex) : Connected G.circuitStep C.cutPairing a b := by
  obtain ⟨n, rfl⟩ := ((G.rotation_sameCycle_iff a b).mpr hv).exists_nat_pow_eq
  clear hv
  induction n with
  | zero => exact Connected.refl _
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply]
    apply ih.trans (C.cut_connected_rotation_of_unmarked ?_)
    intro hm
    have hc := C.marked_onCircuitVertex hm
    rw [G.vertex_rotation_pow] at hc
    exact ha hc

theorem onSide_same_vertex {a b : G.Dart} (ha : ¬ C.OnCircuitVertex a.vertex)
    (hv : a.vertex = b.vertex) (s : Bool) : C.OnSide s a ↔ C.OnSide s b := by
  have hc := C.cut_connected_same_vertex ha hv
  exact ⟨fun h => hc.symm.trans h, fun h => hc.trans h⟩

theorem onSide_twin_iff {a : G.Dart} (ha : ¬ C.Marked a) (s : Bool) :
    C.OnSide s (G.pairing.twin a) ↔ C.OnSide s a := by
  have hc : Connected G.circuitStep C.cutPairing a (G.pairing.twin a) := by
    rw [← C.cutPairing_of_unmarked a ha]
    exact Connected.circuit _
  exact ⟨fun h => hc.trans h, fun h => hc.symm.trans h⟩

theorem sector_onSide_twin {a : G.Dart} {s : Bool} (ha : C.Sector s a) :
    C.OnSide (!s) (G.pairing.twin a) := by
  have ht := (sameCycle_congr (C.edgeTwist * G.rotation) (C.cutPairing * G.circuitStep)
    G.pairing.perm C.cutFace_conjugate (C.port (0, s)) a).mp ha
  have hc := RotationEuler.sameCycle_mul_connected G.circuitStep C.cutPairing ht
  change Connected G.circuitStep C.cutPairing (G.pairing.twin (C.port (0, s)))
    (G.pairing.twin a) at hc
  rw [C.twin_port] at hc
  exact hc.symm.trans (C.cut_marked_connected_of_side (CircuitPermutations.edge C.length (0, s))
    (0, !s) (CircuitPermutations.edge_snd C.length (0, s)))

theorem sector_onSide {a : G.Dart} {s : Bool} (ha : ¬ C.Marked a) (hs : C.Sector s a) :
    C.OnSide (!s) a := (C.onSide_twin_iff ha (!s)).mp (C.sector_onSide_twin hs)

variable (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
  2 * Nat.card (Component G.circuitStep G.pairing.perm))

include hEuler in
theorem onSide_unique {a : G.Dart} {s t : Bool} (hs : C.OnSide s a) (ht : C.OnSide t a) : s = t :=
  (C.cut_marked_connected_iff hEuler (0, s) (0, t)).mp (hs.symm.trans ht)

include hEuler in
theorem sector_iff_onSide {a : G.Dart} (ha : ¬ C.Marked a)
    (hv : C.OnCircuitVertex a.vertex) (s : Bool) : C.Sector s a ↔ C.OnSide (!s) a := by
  constructor
  · exact C.sector_onSide ha
  · intro hs
    obtain ⟨t, ht⟩ := (C.onCircuitVertex_iff_sector a).mp hv
    have he := C.onSide_unique hEuler hs (C.sector_onSide ha ht)
    have he' : s = t := by simpa only [Bool.not_not] using congrArg (fun b : Bool => !b) he
    exact he' ▸ ht

include hEuler in
/-- Exactly the unmarked ports at circuit vertices face the corresponding side. -/
theorem sector_frontier_iff (s : Bool) (a : G.Dart) :
    (C.Sector (!s) a ∧ ¬ C.Marked a) ↔
      (C.OnCircuitVertex a.vertex ∧ ¬ C.Marked a ∧ C.OnSide s a) := by
  constructor
  · rintro ⟨hs, ha⟩
    exact ⟨(C.onCircuitVertex_iff_sector a).mpr ⟨!s, hs⟩, ha,
      by simpa only [Bool.not_not] using C.sector_onSide ha hs⟩
  · rintro ⟨hv, ha, hs⟩
    refine ⟨(C.sector_iff_onSide hEuler ha hv (!s)).mpr ?_, ha⟩
    simpa only [Bool.not_not] using hs

end ThomGame.Pictures.PortGraph.SimpleCircuit
