module

public import ThomGame.Pictures.CircuitGermEuler
public import ThomGame.Pictures.BoundarySwapGraph

/-!
# A genuine diagram for every actual circuit germ

The stored germ frontier runs forward on its lower boundary. Exchanging
the boundary names gives the forward upper-boundary convention required
by graph realization. Reflection then returns a diagram on the exact
original lower word. The complete relation multiset, size and sign are
preserved, without an extra boundary or Euler hypothesis on the germ.
-/

@[expose] public section
namespace ThomGame.Pictures

open Equiv RibbonConnectivity CircularPartition
open scoped BigOperators

variable {R S : Type*} {P : InvolutionPresentation R S}

namespace PortGraph

theorem exists_diagram_of_forward_bottom {w : List S} (G : PortGraph P [] w)
    (hn : ∀ h, 0 < (P.word (G.hubLabel h)).length)
    (hEuler : RotationEuler.count G.rotation G.pairing.perm =
      2 * Nat.card (Component G.rotation G.pairing.perm))
    (hconn : ∀ a b : G.Dart, Connected G.rotation G.pairing.perm a b)
    (hnext : ∀ i : Fin w.length, G.boundaryNext (.inr i) = .inr (finRotate _ i)) :
    ∃ d : Diagram P [] w, (d.labels : Multiset R) =
      ∑ h : G.Hub, ([G.hubLabel h] : Multiset R) := by
  have hr : G.swapBoundary.boundaryNext = boundaryCyclic w [] := by
    ext a
    cases a with
    | inl i =>
      rw [boundaryCyclic_top]
      have he := G.swapBoundary_next (.inr i)
      rw [hnext i] at he
      exact he
    | inr i => exact i.elim0
  have hnc : G.swapBoundary.BoundaryNoncrossing := by
    change OrderedNoncrossing _ _ _
    rw [hr]
    exact ⟨follows_self _, fun a b _ _ _ _ _ _ => boundaryCyclic_sameCycle a b⟩
  have hsees : G.swapBoundary.BoundarySeesComponents := by
    apply G.swapBoundary.boundarySeesComponents_of_one_cycle
    intro a b
    rw [hr]
    exact boundaryCyclic_sameCycle a b
  obtain ⟨d, hd⟩ := G.swapBoundary.exists_diagram_of_connected hn
    (G.swapBoundary_rotationEuler hEuler) (G.swapBoundary_connected hconn) hnc hsees
  exact ⟨d.adjoint, (Multiset.coe_eq_coe.mpr d.labels_adjoint_perm).trans hd⟩

namespace SimpleCircuit

variable {G : PortGraph P [] []} (C : G.SimpleCircuit)
    (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
      2 * Nat.card (Component G.circuitStep G.pairing.perm))

include hEuler in
theorem exists_germ_diagram (s : Bool)
    (hn : ∀ h : C.GermHub s, 0 < (P.word (G.hubLabel h.val)).length) :
    ∃ d : Diagram P [] (C.frontierWord (!s)),
      (d.labels : Multiset R) = ∑ h : C.GermHub s, ([G.hubLabel h.val] : Multiset R) :=
  (C.germGraph hEuler s).exists_diagram_of_forward_bottom hn
    (C.germGraph_rotationEuler hEuler s) (C.germGraph_connected hEuler s)
    (C.germGraph_boundaryNext_bottom hEuler s)

include hEuler in
theorem exists_germ_diagram_preserving (s : Bool)
    (hn : ∀ h : C.GermHub s, 0 < (P.word (G.hubLabel h.val)).length) :
    ∃ d : Diagram P [] (C.frontierWord (!s)),
      (d.labels : Multiset R) = (∑ h : C.GermHub s, ([G.hubLabel h.val] : Multiset R)) ∧
      d.size = Fintype.card (C.GermHub s) ∧ d.sign = (C.germGraph hEuler s).sign := by
  obtain ⟨d, hd⟩ := C.exists_germ_diagram hEuler s hn
  have hadj : (d.adjoint.labels : Multiset R) =
      ∑ h : C.GermHub s, ([G.hubLabel h.val] : Multiset R) :=
    (Multiset.coe_eq_coe.mpr d.labels_adjoint_perm).trans hd
  have hsize := (C.germGraph hEuler s).swapBoundary.diagram_size_of_hub_labels hadj
  have hsign := (C.germGraph hEuler s).swapBoundary.diagram_sign_of_hub_labels hadj
  rw [Diagram.size_adjoint] at hsize
  rw [Diagram.sign_adjoint] at hsign
  exact ⟨d, hd, hsize, hsign⟩

end SimpleCircuit
end PortGraph
end ThomGame.Pictures
