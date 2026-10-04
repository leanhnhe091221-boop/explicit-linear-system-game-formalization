module

public import ThomGame.Pictures.CircuitInteriorEmbedding
public import ThomGame.Pictures.CircuitGermPorts
public import ThomGame.Pictures.CircuitPullback
public import ThomGame.Pictures.BoundarySwapGraph

/-!
# Recovering an actual region circuit in the original closed graph

Boundary swapping is undone on the actual ports. The region embedding
preserves vertex equality away from boundary leaves, which no simple
circuit can use. The resulting original circuit retains every indexed
port and label, and all its vertices avoid the opposite germ.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open RibbonConnectivity

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}

theorem swapBoundaryPorts_vertex (G : PortGraph P u v) (a b : G.Dart) :
    (G.swapBoundaryPorts a).vertex = (G.swapBoundaryPorts b).vertex ↔ a.vertex = b.vertex := by
  rw [← G.swapBoundary.rotation_sameCycle_iff, ← G.rotation_sameCycle_iff]
  exact (FiniteReturn.sameCycle_congr _ _ G.swapBoundaryPorts G.swapBoundary_rotation a b).symm

namespace SimpleCircuit

variable {G : PortGraph P u v}

@[reducible] noncomputable def unswapBoundary (D : G.swapBoundary.SimpleCircuit) : G.SimpleCircuit :=
  D.pullback G.swapBoundaryPorts.toEmbedding (G.swapBoundaryPorts_vertex)
    G.swapBoundary_pairing (fun i => G.swapBoundaryPorts.surjective (D.dart i))

theorem unswapBoundary_port (D : G.swapBoundary.SimpleCircuit) (x : Fin D.length × Bool) :
    G.swapBoundaryPorts (D.unswapBoundary.port x) = D.port x :=
  D.pullback_port G.swapBoundaryPorts.toEmbedding (G.swapBoundaryPorts_vertex)
    G.swapBoundary_pairing (fun i => G.swapBoundaryPorts.surjective (D.dart i)) x

theorem unswapBoundary_face_iff (D : G.swapBoundary.SimpleCircuit) (side : Bool) :
    D.unswapBoundary.BoundsFaceOrbit side ↔ D.BoundsFaceOrbit side := by
  have he := D.unswapBoundary.boundsFaceOrbit_iff_image_orbit G.swapBoundaryPorts.toEmbedding side
    (fun i => G.swapBoundary_circuitStep (D.unswapBoundary.port (i, side)))
  simpa only [BoundsFaceOrbit, Equiv.toEmbedding_apply, D.unswapBoundary_port] using he

variable {G : PortGraph P [] []} (C : G.SimpleCircuit)
  (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
    2 * Nat.card (Component G.circuitStep G.pairing.perm)) (s : Bool)

noncomputable def regionPortEmbedding : (C.regionGraph hEuler s).Dart ↪ G.Dart :=
  (C.regionPorts hEuler s).toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩

theorem regionPortEmbedding_twin (a : (C.regionGraph hEuler s).Dart) :
    G.pairing.twin (C.regionPortEmbedding hEuler s a) =
      C.regionPortEmbedding hEuler s ((C.regionGraph hEuler s).pairing.twin a) :=
  (C.regionGraph_twin hEuler s a).symm

theorem regionPortEmbedding_vertex (a b : (C.regionGraph hEuler s).Dart)
    (ha : ¬ (C.regionGraph hEuler s).IsBoundary a)
    (hb : ¬ (C.regionGraph hEuler s).IsBoundary b) :
    (C.regionPortEmbedding hEuler s a).vertex = (C.regionPortEmbedding hEuler s b).vertex ↔
      a.vertex = b.vertex := by
  cases a with
  | top i => exact (ha trivial).elim
  | bottom i => exact i.elim0
  | hub h i =>
    cases b with
    | top j => exact (hb trivial).elim
    | bottom j => exact j.elim0
    | hub k j =>
      change Sum.inr (Sum.inl h.val) = Sum.inr (Sum.inl k.val) ↔
        Sum.inr (Sum.inl h) = Sum.inr (Sum.inl k)
      simp only [Sum.inr.injEq, Sum.inl.injEq, Subtype.val_inj]
    | joint j t => exact iff_of_false (by intro h; cases h) (by intro h; cases h)
  | joint j t =>
    cases b with
    | top i => exact (hb trivial).elim
    | bottom i => exact i.elim0
    | hub h i => exact iff_of_false (by intro h; cases h) (by intro h; cases h)
    | joint k v =>
      change Sum.inr (Sum.inr j.val) = Sum.inr (Sum.inr k.val) ↔
        Sum.inr (Sum.inr j) = Sum.inr (Sum.inr k)
      simp only [Sum.inr.injEq, Subtype.val_inj]

theorem regionPortEmbedding_interior (a : (C.regionGraph hEuler s).Dart)
    (ha : ¬ (C.regionGraph hEuler s).IsBoundary a) :
    C.InteriorVertex s (C.regionPortEmbedding hEuler s a).vertex := by
  cases a with
  | top i => exact (ha trivial).elim
  | bottom i => exact i.elim0
  | hub h i => exact h.property
  | joint j b => exact j.property

theorem regionPortEmbedding_rotation (a : (C.regionGraph hEuler s).Dart)
    (ha : ¬ (C.regionGraph hEuler s).IsBoundary a) :
    G.rotation (C.regionPortEmbedding hEuler s a) =
      C.regionPortEmbedding hEuler s ((C.regionGraph hEuler s).rotation a) := by
  cases a with
  | top i => exact (ha trivial).elim
  | bottom i => exact i.elim0
  | hub h i => rfl
  | joint j b => rfl

theorem regionPortEmbedding_step (a : (C.regionGraph hEuler s).Dart)
    (ha : ¬ (C.regionGraph hEuler s).IsBoundary ((C.regionGraph hEuler s).pairing.twin a)) :
    G.circuitStep (C.regionPortEmbedding hEuler s a) =
      C.regionPortEmbedding hEuler s ((C.regionGraph hEuler s).circuitStep a) := by
  rw [G.circuitStep_apply, C.regionPortEmbedding_twin, C.regionPortEmbedding_rotation hEuler s _ ha]
  rfl

include hEuler in
theorem interiorVertex_not_opposite_germ {x : G.Vertex} (hx : C.InteriorVertex s x) :
    ¬ C.GermVertex (!s) x := by
  rintro (hc | hi)
  · exact hx.1 hc
  · exact (Bool.not_eq_self s).mp (C.interiorVertex_side_unique hEuler hx hi).symm

@[reducible] noncomputable def recoverRegionCircuit
    (D : (C.regionGraph hEuler s).SimpleCircuit) : G.SimpleCircuit :=
  D.mapInterior (C.regionPortEmbedding hEuler s) (C.regionPortEmbedding_vertex hEuler s)
    (C.regionPortEmbedding_twin hEuler s)

theorem recoverRegionCircuit_port (D : (C.regionGraph hEuler s).SimpleCircuit)
    (x : Fin D.length × Bool) :
    (C.recoverRegionCircuit hEuler s D).port x = C.regionPortEmbedding hEuler s (D.port x) :=
  D.mapInterior_port _ _ _ x

theorem recoverRegionCircuit_label (D : (C.regionGraph hEuler s).SimpleCircuit)
    (x : Fin D.length × Bool) :
    Port.label G.jointLabel ((C.recoverRegionCircuit hEuler s D).port x) =
      Port.label (C.regionGraph hEuler s).jointLabel (D.port x) := by
  rw [C.recoverRegionCircuit_port]
  exact C.regionPortMap_label hEuler s _

theorem recoverRegionCircuit_interior (D : (C.regionGraph hEuler s).SimpleCircuit)
    (x : Fin D.length × Bool) :
    C.InteriorVertex s ((C.recoverRegionCircuit hEuler s D).port x).vertex := by
  rw [C.recoverRegionCircuit_port]
  exact C.regionPortEmbedding_interior hEuler s _ (D.port_not_boundary _ _)

theorem recoverRegionCircuit_not_germ (D : (C.regionGraph hEuler s).SimpleCircuit)
    (x : Fin D.length × Bool) :
    ¬ C.GermVertex (!s) ((C.recoverRegionCircuit hEuler s D).port x).vertex :=
  C.interiorVertex_not_opposite_germ hEuler s (C.recoverRegionCircuit_interior hEuler s D x)

theorem recoverRegionCircuit_face_iff (D : (C.regionGraph hEuler s).SimpleCircuit) (side : Bool) :
    (C.recoverRegionCircuit hEuler s D).BoundsFaceOrbit side ↔ D.BoundsFaceOrbit side := by
  have he := D.boundsFaceOrbit_iff_image_orbit (C.regionPortEmbedding hEuler s) side
    (fun i => C.regionPortEmbedding_step hEuler s _ (D.twin_port_not_boundary (i, side)))
  simpa only [BoundsFaceOrbit, C.recoverRegionCircuit_port] using he.symm

noncomputable def swappedRegionPortEmbedding : (C.regionGraph hEuler s).swapBoundary.Dart ↪ G.Dart :=
  (C.regionGraph hEuler s).swapBoundaryPorts.symm.toEmbedding.trans (C.regionPortEmbedding hEuler s)

@[reducible] noncomputable def recoverSwappedRegionCircuit
    (D : (C.regionGraph hEuler s).swapBoundary.SimpleCircuit) : G.SimpleCircuit :=
  C.recoverRegionCircuit hEuler s D.unswapBoundary

theorem recoverSwappedRegionCircuit_port (D : (C.regionGraph hEuler s).swapBoundary.SimpleCircuit)
    (x : Fin D.length × Bool) :
    (C.recoverSwappedRegionCircuit hEuler s D).port x =
      C.swappedRegionPortEmbedding hEuler s (D.port x) := by
  change (C.recoverRegionCircuit hEuler s D.unswapBoundary).port x =
    C.regionPortEmbedding hEuler s ((C.regionGraph hEuler s).swapBoundaryPorts.symm (D.port x))
  rw [C.recoverRegionCircuit_port, ← D.unswapBoundary_port x, Equiv.symm_apply_apply]

theorem recoverSwappedRegionCircuit_label (D : (C.regionGraph hEuler s).swapBoundary.SimpleCircuit)
    (x : Fin D.length × Bool) :
    Port.label G.jointLabel ((C.recoverSwappedRegionCircuit hEuler s D).port x) =
      Port.label (C.regionGraph hEuler s).swapBoundary.jointLabel (D.port x) := by
  change Port.label G.jointLabel ((C.recoverRegionCircuit hEuler s D.unswapBoundary).port x) = _
  rw [C.recoverRegionCircuit_label, ← D.unswapBoundary_port x]
  exact (Port.swapBoundary_label _ _).symm

theorem recoverSwappedRegionCircuit_not_germ (D : (C.regionGraph hEuler s).swapBoundary.SimpleCircuit)
    (x : Fin D.length × Bool) :
    ¬ C.GermVertex (!s) ((C.recoverSwappedRegionCircuit hEuler s D).port x).vertex :=
  C.recoverRegionCircuit_not_germ hEuler s D.unswapBoundary x

theorem recoverSwappedRegionCircuit_face_iff (D : (C.regionGraph hEuler s).swapBoundary.SimpleCircuit)
    (side : Bool) :
    (C.recoverSwappedRegionCircuit hEuler s D).BoundsFaceOrbit side ↔ D.BoundsFaceOrbit side :=
  (C.recoverRegionCircuit_face_iff hEuler s D.unswapBoundary side).trans (D.unswapBoundary_face_iff side)

end SimpleCircuit
end ThomGame.Pictures.PortGraph
