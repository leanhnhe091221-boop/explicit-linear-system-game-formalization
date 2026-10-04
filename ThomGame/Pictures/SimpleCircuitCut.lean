module

public import ThomGame.Pictures.SimpleCircuitMarks
public import ThomGame.Pictures.RotationEulerGraph

/-!
# Cutting the edges of a simple circuit in the dual rotation graph

The edge twist reverses exactly the marked edges. Multiplying it with
the original edge pairing leaves each cut port fixed and preserves all
uncut pairings. The exact first-return computations give an increase of
two in the dual Euler count. For an original graph attaining the Euler
upper bound, at least one additional connected component is required.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open Equiv FiniteReturn MarkedReturn RibbonConnectivity

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  {G : PortGraph P u v} (C : G.SimpleCircuit)

open scoped Classical

noncomputable def edgeTwist : Perm G.Dart where
  toFun a := if C.Marked a then G.pairing.twin a else a
  invFun a := if C.Marked a then G.pairing.twin a else a
  left_inv a := by
    by_cases ha : C.Marked a
    · simp only [ha, ite_true, C.marked_twin_iff]
      exact G.pairing.involutive a
    · simp only [ha, ite_false]
  right_inv a := by
    by_cases ha : C.Marked a
    · simp only [ha, ite_true, C.marked_twin_iff]
      exact G.pairing.involutive a
    · simp only [ha, ite_false]

theorem edgeTwist_of_marked {a : G.Dart} (ha : C.Marked a) :
    C.edgeTwist a = G.pairing.twin a := by
  change (if C.Marked a then G.pairing.twin a else a) = G.pairing.twin a
  rw [ite_eq_left ha]

theorem edgeTwist_of_unmarked (a : G.Dart) (ha : ¬ C.Marked a) : C.edgeTwist a = a := by
  change (if C.Marked a then G.pairing.twin a else a) = a
  rw [ite_eq_right ha]

theorem edgeTwist_involutive : Function.Involutive C.edgeTwist := C.edgeTwist.left_inv

theorem edgeTwist_twin (a : G.Dart) :
    C.edgeTwist (G.pairing.twin a) = G.pairing.twin (C.edgeTwist a) := by
  by_cases ha : C.Marked a
  · rw [C.edgeTwist_of_marked ((C.marked_twin_iff a).mpr ha), C.edgeTwist_of_marked ha]
  · rw [C.edgeTwist_of_unmarked _ (fun h => ha ((C.marked_twin_iff a).mp h)),
      C.edgeTwist_of_unmarked _ ha]

theorem edgeTwist_port (x : Fin C.length × Bool) :
    C.edgeTwist (C.port x) = C.port (CircuitPermutations.edge C.length x) := by
  rw [C.edgeTwist_of_marked (show C.Marked (C.port x) from ⟨x, rfl⟩), C.twin_port]

theorem pairing_return_edgeTwist (x : Subtype C.Marked) :
    (perm G.pairing.perm C.Marked x).val = C.edgeTwist x.val := by
  obtain ⟨y, rfl⟩ := C.portEquiv.surjective x
  rw [C.pairing_return_port, portEquiv_val, portEquiv_val, C.edgeTwist_port]

theorem return_edgeTwist_mul (f : Perm G.Dart) :
    perm (C.edgeTwist * f) C.Marked = perm G.pairing.perm C.Marked * perm f C.Marked :=
  perm_mul_retained f C.Marked C.edgeTwist (perm G.pairing.perm C.Marked)
    C.edgeTwist_of_unmarked C.pairing_return_edgeTwist

theorem twisted_rotation_return_port (x : Fin C.length × Bool) :
    perm (C.edgeTwist * G.rotation) C.Marked (C.portEquiv x) =
      C.portEquiv (CircuitPermutations.sides C.length x) := by
  rw [C.return_edgeTwist_mul, Perm.mul_apply, C.rotation_return_port, C.pairing_return_port]
  rfl

theorem twisted_rotation_return_card :
    Nat.card (Orbit (perm (C.edgeTwist * G.rotation) C.Marked)) = 2 := by
  rw [← Nat.card_congr (orbitEquiv (CircuitPermutations.sides C.length)
    (perm (C.edgeTwist * G.rotation) C.Marked) C.portEquiv C.twisted_rotation_return_port),
    CircuitPermutations.sides_orbit_card]

/-- The n visited vertex orbits are replaced by two orbits. -/
theorem twisted_rotation_orbit_card :
    Nat.card (Orbit (C.edgeTwist * G.rotation)) + C.length =
      Nat.card (Orbit G.rotation) + 2 := by
  have h := orbit_card_mul_balance G.rotation C.Marked C.edgeTwist C.edgeTwist_of_unmarked
  rwa [C.rotation_return_card, C.twisted_rotation_return_card] at h

/-- The edge involution of the cut dual graph; cut ports are fixed. -/
noncomputable def cutPairing : Perm G.Dart := C.edgeTwist * G.pairing.perm

theorem cutPairing_of_marked {a : G.Dart} (ha : C.Marked a) : C.cutPairing a = a := by
  change C.edgeTwist (G.pairing.twin a) = a
  rw [C.edgeTwist_of_marked ((C.marked_twin_iff a).mpr ha), G.pairing.involutive]

theorem cutPairing_of_unmarked (a : G.Dart) (ha : ¬ C.Marked a) :
    C.cutPairing a = G.pairing.twin a := by
  change C.edgeTwist (G.pairing.twin a) = G.pairing.twin a
  exact C.edgeTwist_of_unmarked _ (fun h => ha ((C.marked_twin_iff a).mp h))

theorem cutPairing_involutive : Function.Involutive C.cutPairing := by
  intro a
  by_cases ha : C.Marked a
  · rw [C.cutPairing_of_marked ha, C.cutPairing_of_marked ha]
  · rw [C.cutPairing_of_unmarked _ ha,
      C.cutPairing_of_unmarked _ (fun h => ha ((C.marked_twin_iff a).mp h)), G.pairing.involutive]

theorem cutPairing_return : perm C.cutPairing C.Marked = 1 := by
  apply Equiv.ext
  intro x
  obtain ⟨y, rfl⟩ := C.portEquiv.surjective x
  change perm (C.edgeTwist * G.pairing.perm) C.Marked (C.portEquiv y) = C.portEquiv y
  rw [C.return_edgeTwist_mul, Perm.mul_apply, C.pairing_return_port, C.pairing_return_port,
    CircuitPermutations.edge_involutive]

/-- Each cut two-port edge orbit becomes two singleton orbits. -/
theorem cutPairing_orbit_card :
    Nat.card (Orbit C.cutPairing) = Nat.card (Orbit G.pairing.perm) + C.length := by
  have h := orbit_card_mul_balance G.pairing.perm C.Marked C.edgeTwist C.edgeTwist_of_unmarked
  change Nat.card (Orbit C.cutPairing) + Nat.card (Orbit (perm G.pairing.perm C.Marked)) =
    Nat.card (Orbit G.pairing.perm) + Nat.card (Orbit (perm C.cutPairing C.Marked)) at h
  rw [C.pairing_return_card, C.cutPairing_return,
    Nat.card_congr (orbitOneEquiv (Subtype C.Marked)), C.marked_card] at h
  omega

theorem cutFace_conjugate (a : G.Dart) :
    (C.cutPairing * G.circuitStep) (G.pairing.perm a) =
      G.pairing.perm ((C.edgeTwist * G.rotation) a) := by
  change C.edgeTwist (G.pairing.twin (G.rotation (G.pairing.twin (G.pairing.twin a)))) =
    G.pairing.twin (C.edgeTwist (G.rotation a))
  rw [G.pairing.involutive, C.edgeTwist_twin]

noncomputable def cutFaceOrbitEquiv :
    Orbit (C.edgeTwist * G.rotation) ≃ Orbit (C.cutPairing * G.circuitStep) :=
  orbitEquiv (C.edgeTwist * G.rotation) (C.cutPairing * G.circuitStep)
    G.pairing.perm C.cutFace_conjugate

/-- Cutting a simple circuit increases the dual Euler count by two. -/
theorem cut_euler_count :
    RotationEuler.count G.circuitStep C.cutPairing =
      RotationEuler.count G.circuitStep G.pairing.perm + 2 := by
  have hv := C.twisted_rotation_orbit_card
  have he := C.cutPairing_orbit_card
  have hf := Nat.card_congr C.cutFaceOrbitEquiv
  have ho := Nat.card_congr (orbitEquiv G.rotation (G.pairing.perm * G.circuitStep)
    G.pairing.perm (fun a => by
      change G.pairing.twin (G.rotation (G.pairing.twin (G.pairing.twin a))) =
        G.pairing.twin (G.rotation a)
      rw [G.pairing.involutive]))
  unfold RotationEuler.count
  omega

theorem cut_components_increase
    (h : RotationEuler.count G.circuitStep G.pairing.perm =
      2 * Nat.card (Component G.circuitStep G.pairing.perm)) :
    Nat.card (Component G.circuitStep G.pairing.perm) + 1 ≤
      Nat.card (Component G.circuitStep C.cutPairing) := by
  have hb := RotationEuler.count_le_twice_components G.circuitStep C.cutPairing C.cutPairing_involutive
  rw [C.cut_euler_count, h] at hb
  omega

end ThomGame.Pictures.PortGraph.SimpleCircuit
