module

public import ThomGame.Pictures.BoundaryCappingEuler
public import ThomGame.Pictures.GraphBoundaryComponents

/-!
# Capping the prescribed outer boundary of a connected port graph

Boundary order and the boundary-component correspondence identify the
actual return permutation with the specified circular order. Reversing
that order on the boundary leaves preserves Euler count and connectedness.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv RibbonConnectivity CircularPartition
open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
    (G : PortGraph P u v)

theorem boundaryNext_eq_cyclic (hnc : G.BoundaryNoncrossing)
    (hsees : G.BoundarySeesComponents)
    (hconn : ∀ x y : G.Dart, Connected G.rotation G.pairing.perm x y) :
    G.boundaryNext = boundaryCyclic u v := by
  apply hnc.follows.unique (follows_self _)
  intro a b
  constructor
  · intro _; exact boundaryCyclic_sameCycle a b
  · intro _
    apply (FiniteReturn.sameCycle_congr _ _ G.boundaryPorts G.boundaryPorts_next a b).mpr
    apply (MarkedReturn.sameCycle_iff _ _ _ _).mpr
    apply (hsees (G.boundaryPorts a) (G.boundaryPorts b)).mp
    rw [← G.rotation_mul_pairing]
    exact (RotationEuler.connected_rotation_iff _ _ G.pairing.involutive _ _).mp (hconn _ _)

noncomputable def cappingTargets : Perm G.Dart :=
  Perm.extendDomain (boundaryCyclic u v).symm G.boundaryPorts

noncomputable def cappingReturn : Perm {x : G.Dart // G.IsBoundary x} :=
  (G.boundaryPorts.symm.trans (boundaryCyclic u v).symm).trans G.boundaryPorts

noncomputable def cappedRotation : Perm G.Dart := G.cappingTargets * G.rotation

theorem cappingTargets_unmarked (x : G.Dart) (hx : ¬ G.IsBoundary x) :
    G.cappingTargets x = x :=
  Perm.extendDomain_apply_not_subtype _ _ hx

theorem cappingTargets_boundary (i : BoundaryIndex u v) :
    G.cappingTargets (G.boundaryDart i) =
      G.boundaryDart ((boundaryCyclic u v).symm i) :=
  Perm.extendDomain_apply_image _ _ i

theorem cappingReturn_val (x : {x : G.Dart // G.IsBoundary x}) :
    (G.cappingReturn x).val = G.cappingTargets x.val := by
  obtain ⟨i, rfl⟩ := G.boundaryPorts.surjective x
  change (G.boundaryPorts ((boundaryCyclic u v).symm
    (G.boundaryPorts.symm (G.boundaryPorts i)))).val = _
  rw [Equiv.symm_apply_apply]
  exact (G.cappingTargets_boundary i).symm

theorem rotation_boundary (x : G.Dart) (hx : G.IsBoundary x) : G.rotation x = x := by
  cases x <;> first | rfl | exact hx.elim

theorem return_eq_cappingReturn_inv (hnext : G.boundaryNext = boundaryCyclic u v) :
    MarkedReturn.perm (G.rotation * G.pairing.perm) G.IsBoundary = G.cappingReturn⁻¹ := by
  rw [G.rotation_mul_pairing]
  ext x
  obtain ⟨i, rfl⟩ := G.boundaryPorts.surjective x
  rw [G.boundaryPorts_next, hnext]
  change (G.boundaryPorts (boundaryCyclic u v i)).val =
    (G.boundaryPorts (boundaryCyclic u v (G.boundaryPorts.symm (G.boundaryPorts i)))).val
  rw [Equiv.symm_apply_apply]

theorem cappedRotation_count (hnext : G.boundaryNext = boundaryCyclic u v) :
    RotationEuler.count G.cappedRotation G.pairing.perm =
      RotationEuler.count G.rotation G.pairing.perm :=
  RotationEuler.count_cap_boundary G.rotation G.pairing.perm G.IsBoundary
    G.cappingTargets G.cappingReturn G.rotation_boundary G.cappingTargets_unmarked
    G.cappingReturn_val G.pairing.involutive (G.return_eq_cappingReturn_inv hnext)

theorem cappedRotation_connected {x y : G.Dart}
    (h : Connected G.rotation G.pairing.perm x y) :
    Connected G.cappedRotation G.pairing.perm x y :=
  RotationEuler.connected_cap_boundary G.rotation G.pairing.perm G.IsBoundary
    G.cappingTargets G.rotation_boundary G.cappingTargets_unmarked h

theorem cappedRotation_component_card
    (hconn : ∀ x y : G.Dart, Connected G.rotation G.pairing.perm x y) :
    Nat.card (Component G.cappedRotation G.pairing.perm) =
      Nat.card (Component G.rotation G.pairing.perm) := by
  exact Nat.card_congr (componentEquiv _ _ _ _
    (fun x y => ⟨fun _ => hconn x y, G.cappedRotation_connected⟩))

theorem cappedRotation_saturated (hnext : G.boundaryNext = boundaryCyclic u v)
    (hconn : ∀ x y : G.Dart, Connected G.rotation G.pairing.perm x y)
    (hEuler : RotationEuler.count G.rotation G.pairing.perm =
      2 * Nat.card (Component G.rotation G.pairing.perm)) :
    RotationEuler.count G.cappedRotation G.pairing.perm =
      2 * Nat.card (Component G.cappedRotation G.pairing.perm) := by
  rw [G.cappedRotation_count hnext, G.cappedRotation_component_card hconn, hEuler]

end ThomGame.Pictures.PortGraph
