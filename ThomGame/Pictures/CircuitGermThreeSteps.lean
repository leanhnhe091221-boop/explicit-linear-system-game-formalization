module

public import ThomGame.Pictures.CircuitGermBoundaryOrder
public import ThomGame.Pictures.BoundaryQuadConstruction

/-!
# Three face steps through an actual germ

An outward entry, one marked edge, and an outward exit give an actual
quadrilateral on the top boundary of the germ. All three dart equations
refer to the original graph, with its stored boundary enumeration.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

variable {R S : Type*} {P : InvolutionPresentation R S} {G : PortGraph P [] []}

theorem exists_hub_dart [IsEmpty G.Joint] (a : G.Dart) :
    ∃ (h : G.Hub) (i : Fin (P.word (G.hubLabel h)).length), a = .hub h i := by
  cases a with
  | top i => exact i.elim0
  | bottom i => exact i.elim0
  | hub h i => exact ⟨h, i, rfl⟩
  | joint j b => exact isEmptyElim j

namespace SimpleCircuit

open RibbonConnectivity

variable (C : G.SimpleCircuit)
  (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
    2 * Nat.card (Component G.circuitStep G.pairing.perm)) (s : Bool)

noncomputable def germTopInternalPort (a : {a : G.Dart // C.GermVertex s a.vertex}) :
    (C.germGraph hEuler s).swapBoundary.Dart :=
  (C.germGraph hEuler s).swapBoundaryPorts (C.germInternalPort hEuler s a)

theorem germTopInternalPort_hub (h : C.GermHub s)
    (i : Fin (P.word (G.hubLabel h.val)).length) :
    C.germTopInternalPort hEuler s ⟨.hub h.val i, h.property⟩ = .hub h i := by
  unfold germTopInternalPort
  rw [C.germInternalPort_hub]
  rfl

theorem germTopInternalPort_step
    (a b : {a : G.Dart // C.GermVertex s a.vertex})
    (ha : C.Marked a.val) (hab : G.circuitStep a.val = b.val) :
    (C.germGraph hEuler s).swapBoundary.circuitStep (C.germTopInternalPort hEuler s a) =
      C.germTopInternalPort hEuler s b := by
  unfold germTopInternalPort
  rw [(C.germGraph hEuler s).swapBoundary_circuitStep]
  apply congrArg (C.germGraph hEuler s).swapBoundaryPorts
  rw [(C.germGraph hEuler s).circuitStep_apply,
    C.germGraph_twin_internal_uncut hEuler s a (Or.inl ha), C.germInternalPort_rotation]
  exact congrArg (C.germInternalPort hEuler s) (Subtype.ext hab)

theorem germGraph_three_steps (x : G.Dart) (hx : C.Frontier (!s) x)
    (hy : C.Marked (G.rotation x))
    (hz : C.Frontier (!s) (G.circuitStep (G.rotation x))) :
    let first : (C.germGraph hEuler s).Dart :=
      .bottom ((C.boundaryEnumeration (!s)).symm ⟨x, hx⟩)
    let middle := C.germInternalPort hEuler s
      ⟨G.rotation x, Or.inl (C.marked_onCircuitVertex hy)⟩
    let last := C.germInternalPort hEuler s
      ⟨G.circuitStep (G.rotation x),
        (C.germ_vertex_port_iff hEuler s _).mpr (Or.inr hz)⟩
    (C.germGraph hEuler s).circuitStep first = middle ∧
      (C.germGraph hEuler s).circuitStep middle = last ∧
      (C.germGraph hEuler s).circuitStep last =
        .bottom ((C.boundaryEnumeration (!s)).symm ⟨G.circuitStep (G.rotation x), hz⟩) := by
  have hs : C.Sector s x := by simpa only [Bool.not_not] using hx.1
  refine ⟨?_, ?_, ?_⟩
  · have he := C.germSectorExit_step hEuler s ⟨x, hs⟩
    rw [C.germSectorExit_outward hEuler s ⟨x, hs⟩ hx.2] at he
    exact he
  · rw [(C.germGraph hEuler s).circuitStep_apply,
      C.germGraph_twin_internal_uncut hEuler s _ (Or.inl hy), C.germInternalPort_rotation]
    rfl
  · rw [(C.germGraph hEuler s).circuitStep_apply,
      C.germGraph_twin_internal_outward hEuler s _ hz]
    rfl

theorem germTopInternalPort_eq_hub [IsEmpty G.Joint]
    (a : {a : G.Dart // C.GermVertex s a.vertex}) :
    ∃ (h : C.GermHub s) (i : Fin (P.word (G.hubLabel h.val)).length),
      C.germTopInternalPort hEuler s a = .hub h i ∧ a.val = .hub h.val i := by
  obtain ⟨h, i, he⟩ := exists_hub_dart a.val
  have hh : C.GermVertex s (.inr (.inl h)) := by simpa only [he, Port.vertex] using a.property
  refine ⟨⟨h, hh⟩, i, ?_, he⟩
  have ha : a = ⟨.hub h i, hh⟩ := Subtype.ext he
  rw [ha]
  exact C.germTopInternalPort_hub hEuler s ⟨h, hh⟩ i

theorem germTop_quad_of_crossing [IsEmpty G.Joint]
    (x : G.Dart) (hx : C.Frontier (!s) x)
    (hy : C.Marked (G.rotation x))
    (hz : C.Frontier (!s) (G.circuitStep (G.rotation x)))
    (hv : (G.pairing.twin (G.rotation x)).vertex ≠ (G.rotation x).vertex) :
    ∃ q : (C.germGraph hEuler s).swapBoundary.BoundaryQuadPath,
      q.firstDart = .top ((C.boundaryEnumeration (!s)).symm ⟨x, hx⟩) ∧
      q.middleDart = C.germTopInternalPort hEuler s
        ⟨G.rotation x, Or.inl (C.marked_onCircuitVertex hy)⟩ ∧
      q.lastDart = C.germTopInternalPort hEuler s
        ⟨G.circuitStep (G.rotation x),
          (C.germ_vertex_port_iff hEuler s _).mpr (Or.inr hz)⟩ := by
  let E := C.germGraph hEuler s
  let y : {a : G.Dart // C.GermVertex s a.vertex} :=
    ⟨G.rotation x, Or.inl (C.marked_onCircuitVertex hy)⟩
  let z : {a : G.Dart // C.GermVertex s a.vertex} :=
    ⟨G.circuitStep (G.rotation x), (C.germ_vertex_port_iff hEuler s _).mpr (Or.inr hz)⟩
  obtain ⟨h, i, hi, hi'⟩ := C.germTopInternalPort_eq_hub hEuler s y
  obtain ⟨k, j, hj, hj'⟩ := C.germTopInternalPort_eq_hub hEuler s z
  have hhk : h ≠ k := by
    intro he
    apply hv
    rw [← G.vertex_circuitStep, ← show z.val = G.circuitStep (G.rotation x) from rfl,
      hj', ← show y.val = G.rotation x from rfl, hi']
    change (Sum.inr (Sum.inl k.val) : G.Vertex) = Sum.inr (Sum.inl h.val)
    exact congrArg (fun h : C.GermHub s => (Sum.inr (Sum.inl h.val) : G.Vertex)) he.symm
  obtain ⟨h₁, h₂, h₃⟩ := C.germGraph_three_steps hEuler s x hx hy hz
  let start : BoundaryIndex (C.frontierWord (!s)) [] :=
    .inl ((C.boundaryEnumeration (!s)).symm ⟨x, hx⟩)
  let finish : BoundaryIndex (C.frontierWord (!s)) [] :=
    .inl ((C.boundaryEnumeration (!s)).symm ⟨G.circuitStep (G.rotation x), hz⟩)
  have he₁ : E.swapBoundary.circuitStep (E.swapBoundary.boundaryDart start) = .hub h i := by
    exact (E.swapBoundary_circuitStep
      (.bottom ((C.boundaryEnumeration (!s)).symm ⟨x, hx⟩))).trans
        ((congrArg E.swapBoundaryPorts h₁).trans hi)
  have he₂ : E.swapBoundary.circuitStep (.hub h i) = .hub k j := by
    rw [← hi]
    exact (E.swapBoundary_circuitStep (C.germInternalPort hEuler s y)).trans
      ((congrArg E.swapBoundaryPorts h₂).trans hj)
  have he₃ : E.swapBoundary.circuitStep (.hub k j) = E.swapBoundary.boundaryDart finish := by
    rw [← hj]
    exact (E.swapBoundary_circuitStep (C.germInternalPort hEuler s z)).trans
      (congrArg E.swapBoundaryPorts h₃)
  let q := BoundaryQuadPath.ofThreeSteps
    (E.forwardBottom_swapBoundary_next (C.germGraph_boundaryNext_bottom hEuler s))
    start finish h k i j he₁ he₂ he₃ hhk
  exact ⟨q, rfl, hi.symm, hj.symm⟩

end SimpleCircuit
end ThomGame.Pictures.PortGraph
