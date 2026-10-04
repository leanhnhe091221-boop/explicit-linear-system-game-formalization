module

public import ThomGame.Pictures.RowEdgeSwitchCovers
public import ThomGame.Pictures.CircuitFaceSteps

/-!
# Faciality of every rim after an oriented edge split

Every new oriented rim orbit refines an old one. At each new circuit
vertex the outgoing port and its unique other rim port agree with the
old circuit. The unchanged local rotation therefore preserves every
facial corner, including both circuits created by the split.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.RowEdgeSwitch

open Equiv RibbonConnectivity
open scoped Classical

variable {R S : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
  {G : SolutionGroup.RowGraph A [] []} (s : G.RowEdgeSwitch)
  (γ : Hypergraph.Cycle A.hypergraph)

theorem rimWalk_of_avoids (h : Port.label G.jointLabel s.first ∉ Set.range γ.edge) :
    s.graph.rimWalk γ (by simp) (by simp) = G.rimWalk γ (by simp) (by simp) := by
  unfold rimWalk
  rw [s.rimPairing_of_avoids γ h, s.rimVertexPairing_eq]
  rfl

theorem rimWalk_inverse (ha : Port.label G.jointLabel s.first ∈ Set.range γ.edge) :
    (s.graph.rimWalk γ (by simp) (by simp))⁻¹ =
      PairingCycles.switchedWalk (G.rimVertexPairing γ (by simp) (by simp)) (G.rimPairing γ)
        ⟨s.first, ha⟩ ⟨s.second, s.label_eq ▸ ha⟩ := by
  change (s.graph.rimPairing γ).perm * (s.graph.rimVertexPairing γ (by simp) (by simp)).perm = _
  rw [s.rimPairing_perm γ ha, s.rimVertexPairing_eq]
  exact (PairingCycles.switchedWalk_vertex
    (G.rimVertexPairing γ (by simp) (by simp)) (G.rimPairing γ)
    ⟨s.first, ha⟩ ⟨s.second, s.label_eq ▸ ha⟩).symm

theorem rimWalk_refines (ha : Port.label G.jointLabel s.first ∈ Set.range γ.edge)
    (h : (G.rimWalk γ (by simp) (by simp)).SameCycle
      ⟨s.first, ha⟩ ⟨s.second, s.label_eq ▸ ha⟩)
    {x y : G.RimDart γ} (hxy : (s.graph.rimWalk γ (by simp) (by simp)).SameCycle x y) :
    (G.rimWalk γ (by simp) (by simp)).SameCycle x y := by
  have hab : (⟨s.first, ha⟩ : G.RimDart γ) ≠ ⟨s.second, s.label_eq ▸ ha⟩ :=
    fun he => s.first_ne_second (congrArg Subtype.val he)
  have hi := hxy.inv
  rw [s.rimWalk_inverse γ ha] at hi
  exact (PairingCycles.switchedWalk_refines
    (G.rimVertexPairing γ (by simp) (by simp)) (G.rimPairing γ) hab h.inv hi).inv

variable (hr : ∀ x y : G.RimDart γ,
  (s.graph.rimWalk γ (by simp) (by simp)).SameCycle x y →
    (G.rimWalk γ (by simp) (by simp)).SameCycle x y)

include hr in
theorem rimCircuit_ports_subset (a : G.RimDart γ)
    (i : Fin (s.graph.rimSimpleCircuit γ (by simp) (by simp) a).length) :
    ∃ j : Fin (G.rimSimpleCircuit γ (by simp) (by simp) a).length,
      ∀ side : Bool, (s.graph.rimSimpleCircuit γ (by simp) (by simp) a).port (i, side) =
        (G.rimSimpleCircuit γ (by simp) (by simp) a).port (j, side) := by
  let C := s.graph.rimSimpleCircuit γ (by simp) (by simp) a
  let D := G.rimSimpleCircuit γ (by simp) (by simp) a
  let x := OrbitEnumeration.dart (s.graph.rimWalk γ (by simp) (by simp)) a i
  have hx := hr a x (OrbitEnumeration.dart_sameCycle _ a i)
  obtain ⟨j, hj⟩ := (OrbitEnumeration.dart_range (G.rimWalk γ (by simp) (by simp)) a x).mpr hx
  have hout : C.dart i = D.dart j := (congrArg Subtype.val hj).symm
  let z : G.RimDart γ := ⟨D.dart j, G.rimSimpleCircuit_rim γ (by simp) (by simp) a j⟩
  let ci : G.RimDart γ := ⟨C.incoming i,
    C.marked_label_rim γ (s.graph.rimSimpleCircuit_rim γ (by simp) (by simp) a) ⟨(i, true), rfl⟩⟩
  let di : G.RimDart γ := ⟨D.incoming j,
    D.marked_label_rim γ (G.rimSimpleCircuit_rim γ (by simp) (by simp) a) ⟨(j, true), rfl⟩⟩
  have hci : ci = G.rimSwitch γ (by simp) (by simp) z :=
    G.rimSwitch_unique γ (by simp) (by simp) z ci
      ((C.incoming_vertex i).trans (congrArg Port.vertex hout))
      (fun he => C.incoming_ne_outgoing i ((congrArg Subtype.val he).trans hout.symm))
  have hdi : di = G.rimSwitch γ (by simp) (by simp) z :=
    G.rimSwitch_unique γ (by simp) (by simp) z di (D.incoming_vertex j)
      (fun he => D.incoming_ne_outgoing j (congrArg Subtype.val he))
  refine ⟨j, ?_⟩
  intro side
  cases side
  · exact hout
  · exact congrArg Subtype.val (hci.trans hdi.symm)

include hr in
theorem rim_faces_of_refines (hf : ∀ a : G.RimDart γ,
    ∃ side, (G.rimSimpleCircuit γ (by simp) (by simp) a).BoundsFaceOrbit side) :
    ∀ a : s.graph.RimDart γ,
      ∃ side, (s.graph.rimSimpleCircuit γ (by simp) (by simp) a).BoundsFaceOrbit side := by
  intro a
  obtain ⟨side, hside⟩ := hf a
  refine ⟨side, ?_⟩
  apply SimpleCircuit.boundsFaceOrbit_of_corner_rotation
  intro i
  obtain ⟨j, hp⟩ := s.rimCircuit_ports_subset γ hr a i
  rw [s.rotation, hp (!side), hp side]
  exact SimpleCircuit.corner_rotation_of_boundsFaceOrbit _ side hside j

end ThomGame.Pictures.PortGraph.RowEdgeSwitch
