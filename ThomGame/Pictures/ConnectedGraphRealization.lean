module

public import ThomGame.Pictures.OpenGraphBlocks
public import ThomGame.Pictures.SmoothingEuler
public import ThomGame.Pictures.BoundaryOrderSmoothing

/-!
# Realizing a connected graph with its prescribed boundary and hub labels

Subdivision joints are first removed by an actual smoothing trace.
For an empty boundary the closed realization applies; for a nonempty
boundary the distinguished outer block is capped and punctured. The
result is a genuine diagram with the same ordered boundary and relation
multiset. No isomorphism of its port graph with the input is asserted.
-/

@[expose] public section
namespace ThomGame.Pictures

open RibbonConnectivity
open scoped BigOperators

variable {R S : Type*} {P : InvolutionPresentation R S}

namespace PortGraph

variable {u v : List S} (G : PortGraph P u v)

theorem rotationEuler_saturated_iff :
    (RotationEuler.count G.rotation G.pairing.perm =
      2 * Nat.card (Component G.rotation G.pairing.perm)) ↔
      eulerDefect G.pairing.perm G.circuitStep = 0 := by
  have hc := Nat.card_congr
    (RotationEuler.rotationComponentEquiv G.rotation G.pairing.perm G.pairing.involutive)
  rw [G.rotation_mul_pairing] at hc
  rw [G.rotationEuler_eq_eulerCount, hc]
  unfold eulerDefect
  omega

end PortGraph

namespace Smoothing

variable {u v : List S} {G H : PortGraph P u v} {circles : List S}

theorem rotationEuler_saturated (t : Smoothing G H circles)
    (hn : ∀ h, 0 < (P.word (G.hubLabel h)).length)
    (hEuler : RotationEuler.count G.rotation G.pairing.perm =
      2 * Nat.card (Component G.rotation G.pairing.perm)) :
    RotationEuler.count H.rotation H.pairing.perm =
      2 * Nat.card (Component H.rotation H.pairing.perm) := by
  apply H.rotationEuler_saturated_iff.mpr
  rw [t.eulerDefect hn]
  exact G.rotationEuler_saturated_iff.mp hEuler

theorem rotation_connected (t : Smoothing G H circles)
    (hconn : ∀ x y : G.Dart, Connected G.rotation G.pairing.perm x y) :
    ∀ x y : H.Dart, Connected H.rotation H.pairing.perm x y := by
  intro x y
  apply (RotationEuler.connected_rotation_iff _ _ H.pairing.involutive _ _).mpr
  rw [H.rotation_mul_pairing]
  apply (t.connected_iff x y).mpr
  rw [← G.rotation_mul_pairing]
  exact (RotationEuler.connected_rotation_iff _ _ G.pairing.involutive _ _).mp (hconn _ _)

theorem hub_relations (t : Smoothing G H circles) :
    (∑ h : H.Hub, ([H.hubLabel h] : Multiset R)) =
      ∑ g : G.Hub, ([G.hubLabel g] : Multiset R) := by
  exact (Fintype.sum_equiv t.hubEquiv _ _ (fun g => by rw [t.hubLabel])).symm

end Smoothing

namespace PortGraph

variable {w z : List S} (G : PortGraph P w z)

theorem diagram_size_of_hub_labels {d : Diagram P w z}
    (h : (d.labels : Multiset R) = ∑ h : G.Hub, ([G.hubLabel h] : Multiset R)) :
    d.size = Fintype.card G.Hub := by
  simpa [Diagram.size] using congrArg Multiset.card h

theorem diagram_sign_of_hub_labels {d : Diagram P w z}
    (h : (d.labels : Multiset R) = ∑ h : G.Hub, ([G.hubLabel h] : Multiset R)) :
    d.sign = G.sign := by
  let f : Multiset R →+ ZMod 2 := {
    toFun := fun rs => (rs.map P.parity).sum
    map_zero' := rfl
    map_add' := by intro a b; simp }
  have hh := congrArg f h
  rw [map_sum] at hh
  change (Multiset.map P.parity (d.labels : Multiset R)).sum =
    ∑ h : G.Hub, (Multiset.map P.parity ([G.hubLabel h] : Multiset R)).sum at hh
  simpa [Diagram.sign, PortGraph.sign] using hh

variable {w : List S} (G : PortGraph P w [])

theorem exists_diagram_of_connected_reduced [IsEmpty G.Joint]
    (hn : ∀ h, 0 < (P.word (G.hubLabel h)).length)
    (hEuler : RotationEuler.count G.rotation G.pairing.perm =
      2 * Nat.card (Component G.rotation G.pairing.perm))
    (hconn : ∀ x y : G.Dart, Connected G.rotation G.pairing.perm x y)
    (hnc : G.BoundaryNoncrossing) (hsees : G.BoundarySeesComponents) :
    ∃ d : Diagram P w [], (d.labels : Multiset R) =
      ∑ h : G.Hub, ([G.hubLabel h] : Multiset R) := by
  cases w with
  | nil => exact G.exists_closed_diagram_of_rotationEuler hn hEuler hconn
  | cons a w =>
    exact G.exists_diagram_of_rotationEuler_boundary (by simp) hn hEuler hconn hnc hsees

theorem exists_diagram_of_connected
    (hn : ∀ h, 0 < (P.word (G.hubLabel h)).length)
    (hEuler : RotationEuler.count G.rotation G.pairing.perm =
      2 * Nat.card (Component G.rotation G.pairing.perm))
    (hconn : ∀ x y : G.Dart, Connected G.rotation G.pairing.perm x y)
    (hnc : G.BoundaryNoncrossing) (hsees : G.BoundarySeesComponents) :
    ∃ d : Diagram P w [], (d.labels : Multiset R) =
      ∑ h : G.Hub, ([G.hubLabel h] : Multiset R) := by
  obtain ⟨H, circles, ⟨t⟩, hJ⟩ := Smoothing.exists_without_junctions G
  let : IsEmpty H.Joint := hJ
  obtain ⟨d, hd⟩ := H.exists_diagram_of_connected_reduced (t.hub_word_nonempty hn)
    (t.rotationEuler_saturated hn hEuler) (t.rotation_connected hconn)
    (t.boundaryNoncrossing_iff.mpr hnc) (t.boundarySeesComponents_iff.mpr hsees)
  exact ⟨d, hd.trans t.hub_relations⟩

theorem exists_diagram_of_connected_preserving
    (hn : ∀ h, 0 < (P.word (G.hubLabel h)).length)
    (hEuler : RotationEuler.count G.rotation G.pairing.perm =
      2 * Nat.card (Component G.rotation G.pairing.perm))
    (hconn : ∀ x y : G.Dart, Connected G.rotation G.pairing.perm x y)
    (hnc : G.BoundaryNoncrossing) (hsees : G.BoundarySeesComponents) :
    ∃ d : Diagram P w [],
      (d.labels : Multiset R) = (∑ h : G.Hub, ([G.hubLabel h] : Multiset R)) ∧
      d.size = Fintype.card G.Hub ∧ d.sign = G.sign := by
  obtain ⟨d, hd⟩ := G.exists_diagram_of_connected hn hEuler hconn hnc hsees
  exact ⟨d, hd, G.diagram_size_of_hub_labels hd, G.diagram_sign_of_hub_labels hd⟩

end PortGraph
end ThomGame.Pictures
