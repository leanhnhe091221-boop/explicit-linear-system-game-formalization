module

public import ThomGame.Pictures.CircuitGermSmoothing

/-!
# Labels, rotations, vertices and edges of the recovered circuit component

The endpoint bijection of the actual smoothing trace preserves original
port labels and rotations. Consequently it preserves exactly which ports
belong to the same incident vertex or edge. Disconnected components outside
the original circuit component are outside the scope of this recovery.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open Equiv
open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {G : PortGraph P [] []} (C : G.SimpleCircuit)
  (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
    2 * Nat.card (RibbonConnectivity.Component G.circuitStep G.pairing.perm))

noncomputable def gluedProjection (s : Bool) (a : (C.gluedGraph hEuler s).Dart) : G.Dart :=
  C.gluingRawVal s (C.gluedPorts hEuler s a)

include hEuler in
theorem gluingRawVal_germOriginal (s : Bool) (a : {a : G.Dart // C.GermVertex s a.vertex}) :
    C.gluingRawVal s (.inl (C.germOriginal hEuler s a)) = a.val := by
  rcases (C.germ_vertex_port_iff hEuler s a.val).mp a.property with hu | hf
  · rw [C.germOriginal_of_uncut hEuler s a hu]
    rfl
  · rw [C.germOriginal_of_outward hEuler s a hf]
    rfl

include hEuler in
theorem gluedProjection_germ_hub (s : Bool) (h : C.GermHub s)
    (i : Fin (P.word (G.hubLabel h.val)).length) :
    C.gluedProjection hEuler s (.hub (.inl h) i) = .hub h.val i :=
  C.gluingRawVal_germOriginal hEuler s ⟨.hub h.val i, h.property⟩

include hEuler in
theorem gluedProjection_region_hub (s : Bool) (h : C.InteriorHub (!s))
    (i : Fin (P.word (G.hubLabel h.val)).length) :
    C.gluedProjection hEuler s (.hub (.inr h) i) = .hub h.val i := rfl

include hEuler in
theorem gluedProjection_germ_joint (s : Bool) (j : C.GermJoint s) (b : Bool) :
    C.gluedProjection hEuler s (.joint (.inl (.inl j)) b) = .joint j.val b :=
  C.gluingRawVal_germOriginal hEuler s ⟨.joint j.val b, j.property⟩

include hEuler in
theorem gluedProjection_region_joint (s : Bool) (j : C.InteriorJoint (!s)) (b : Bool) :
    C.gluedProjection hEuler s (.joint (.inl (.inr j)) b) = .joint j.val b := rfl

include hEuler in
theorem gluedProjection_seam (s : Bool) (i : Fin (C.frontierWord (!s)).length) (b : Bool) :
    C.gluedProjection hEuler s (.joint (.inr i) b) = (C.boundaryEnumeration (!s) i).val := by
  cases b <;> rfl

include hEuler in
theorem gluedProjection_label (s : Bool) (a : (C.gluedGraph hEuler s).Dart) :
    Port.label G.jointLabel (C.gluedProjection hEuler s a) =
      Port.label (C.gluedGraph hEuler s).jointLabel a := by
  cases a with
  | top i => exact i.elim0
  | bottom i => exact i.elim0
  | hub h i =>
    rcases h with h | h
    · exact congrArg (Port.label G.jointLabel) (C.gluedProjection_germ_hub hEuler s h i)
    · rfl
  | joint j b =>
    rcases j with (j | j) | i
    · rw [C.gluedProjection_germ_joint]
      rfl
    · rfl
    · rw [C.gluedProjection_seam]
      exact C.boundaryEnumeration_label (!s) i

include hEuler in
theorem gluedProjection_rotation (s : Bool) (a : (C.gluedGraph hEuler s).Dart)
    (ha : C.GluedRetained hEuler s a) :
    C.gluedProjection hEuler s ((C.gluedGraph hEuler s).rotation a) =
      G.rotation (C.gluedProjection hEuler s a) := by
  cases a with
  | top i => exact i.elim0
  | bottom i => exact i.elim0
  | hub h i =>
    rcases h with h | h
    · change C.gluedProjection hEuler s (.hub (.inl h) (G.hubRotation h.val i)) = _
      exact (C.gluedProjection_germ_hub hEuler s h (G.hubRotation h.val i)).trans
        (congrArg G.rotation (C.gluedProjection_germ_hub hEuler s h i)).symm
    · rfl
  | joint j b =>
    rcases j with (j | j) | i
    · change C.gluedProjection hEuler s (.joint (.inl (.inl j)) (!b)) = _
      rw [C.gluedProjection_germ_joint, C.gluedProjection_germ_joint]
      rfl
    · rfl
    · exact ((C.gluedRetained_iff hEuler s _).mp ha).elim

include hEuler in
theorem recoveredPorts_val (s : Bool) (a : (C.germReduction hEuler s).graph.Dart) :
    (C.recoveredPorts hEuler s a).val =
      C.gluedProjection hEuler s ((C.germReduction hEuler s).trace.portEmbedding a) :=
  C.gluedComponentPorts_val hEuler s _

include hEuler in
theorem germReduction_port_retained (s : Bool) (a : (C.germReduction hEuler s).graph.Dart) :
    C.GluedRetained hEuler s ((C.germReduction hEuler s).trace.portEmbedding a) :=
  (C.glued_selectedTerminal hEuler s _).mp
    (((C.germReduction hEuler s).trace.selectedTerminalEquiv _
      (C.germReduction hEuler s).removesOnly (C.germReduction hEuler s).clearsSelected) a).property

include hEuler in
theorem recoveredPorts_label (s : Bool) (a : (C.germReduction hEuler s).graph.Dart) :
    Port.label G.jointLabel (C.recoveredPorts hEuler s a).val =
      Port.label (C.germReduction hEuler s).graph.jointLabel a := by
  rw [C.recoveredPorts_val]
  exact (C.gluedProjection_label hEuler s _).trans ((C.germReduction hEuler s).trace.portLabel a)

include hEuler in
theorem recoveredPorts_rotation (s : Bool) (a : (C.germReduction hEuler s).graph.Dart) :
    (C.recoveredPorts hEuler s ((C.germReduction hEuler s).graph.rotation a)).val =
      G.rotation (C.recoveredPorts hEuler s a).val := by
  rw [C.recoveredPorts_val, C.recoveredPorts_val, (C.germReduction hEuler s).trace.portRotation]
  exact C.gluedProjection_rotation hEuler s _ (C.germReduction_port_retained hEuler s a)

include hEuler in
theorem recoveredPorts_vertex_iff (s : Bool) (a b : (C.germReduction hEuler s).graph.Dart) :
    a.vertex = b.vertex ↔ (C.recoveredPorts hEuler s a).val.vertex = (C.recoveredPorts hEuler s b).val.vertex := by
  rw [← (C.germReduction hEuler s).graph.rotation_sameCycle_iff, ← G.rotation_sameCycle_iff]
  let e : (C.germReduction hEuler s).graph.Dart ↪ G.Dart :=
    (C.recoveredPorts hEuler s).toEmbedding.trans (Function.Embedding.subtype _)
  have he : FiniteReturn.Advances G.rotation (C.germReduction hEuler s).graph.rotation e :=
    fun a => Or.inl (C.recoveredPorts_rotation hEuler s a)
  exact he.sameCycle_iff a b

include hEuler in
theorem recoveredPorts_edge_iff (s : Bool) (a b : (C.germReduction hEuler s).graph.Dart) :
    (C.germReduction hEuler s).graph.pairing.edge a = (C.germReduction hEuler s).graph.pairing.edge b ↔
      G.pairing.edge (C.recoveredPorts hEuler s a).val = G.pairing.edge (C.recoveredPorts hEuler s b).val := by
  rw [Pairing.edge_eq_iff, Pairing.edge_eq_iff]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (C.recoveredPorts_twin hEuler s b)
  · rintro (he | he)
    · exact Or.inl ((C.recoveredPorts hEuler s).injective (Subtype.ext he))
    · exact Or.inr ((C.recoveredPorts hEuler s).injective
        (Subtype.ext (he.trans (C.recoveredPorts_twin hEuler s b).symm)))

end ThomGame.Pictures.PortGraph.SimpleCircuit
