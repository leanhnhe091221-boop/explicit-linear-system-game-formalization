module

public import ThomGame.Construction.WheelOddIndependentErasure
public import ThomGame.Pictures.UnsubdividedCircuitRecovery
public import ThomGame.Pictures.CircuitFaceSteps

/-!
# Recovering every rim edge after actual independent-rim erasure

The surviving darts embed at original hubs outside the erased circuit.
Rotations commute on all surviving ports. Every new joint has the
external label, absent from all constellation cycles, so a rim edge
never enters a joint during smoothing and retains its original twin.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures PortGraph Equiv
open scoped Classical

variable {H : SigmaGraph [] []} [IsEmpty H.Joint]
  (a : H.RimDart (numberedWheelCycles oddWheelCycle)) (hi : OddRimIndependentOnly H a)
  {K : SigmaGraph [] []} {circles : List (Fin 1889684)}
  (t : Smoothing (oddIndependentCutGraph a hi) K circles) [IsEmpty K.Joint]

noncomputable def oddIndependentErasurePorts : K.Dart ↪ H.Dart :=
  t.portEmbedding.trans ⟨oddIndependentCutPort a, oddIndependentCutPort_injective a⟩

omit [IsEmpty K.Joint] in
theorem oddIndependentErasurePorts_hub (h : K.Hub) (p : Fin 3) :
    ∃ (g : H.Hub) (q : Fin 3),
      oddIndependentErasurePorts a hi t (.hub h p) = .hub g q ∧
      H.hubLabel g = K.hubLabel h ∧
      g ∉ Set.range (closedSigmaRimCircuit H oddWheelCycle a).hubAt := by
  obtain ⟨g, q, hg, hl⟩ := t.portEmbedding_hub_data h p
  refine ⟨g.val, q, ?_, hl, g.property⟩
  exact congrArg (oddIndependentCutPort a) hg

theorem oddIndependentErasurePorts_rotation (x : K.Dart) :
    oddIndependentErasurePorts a hi t (K.rotation x) =
      H.rotation (oddIndependentErasurePorts a hi t x) := by
  cases x with
  | top j => exact j.elim0
  | bottom j => exact j.elim0
  | joint j side => exact isEmptyElim j
  | hub h p =>
    obtain ⟨g, q, hg, _⟩ := t.portEmbedding_hub_data h p
    change oddIndependentCutPort a (t.portEmbedding (K.rotation (.hub h p))) = _
    rw [t.portRotation]
    change oddIndependentCutPort a ((oddIndependentCutGraph a hi).rotation
      (t.portEmbedding (.hub h p))) = H.rotation (oddIndependentCutPort a (t.portEmbedding (.hub h p)))
    rw [hg]
    rfl

theorem oddIndependentErasurePorts_vertex (x y : K.Dart) :
    (oddIndependentErasurePorts a hi t x).vertex = (oddIndependentErasurePorts a hi t y).vertex ↔
      x.vertex = y.vertex := by
  have h : FiniteReturn.Advances H.rotation K.rotation (oddIndependentErasurePorts a hi t) :=
    fun x => Or.inl (oddIndependentErasurePorts_rotation a hi t x)
  rw [← H.rotation_sameCycle_iff, ← K.rotation_sameCycle_iff]
  exact (h.sameCycle_iff x y).symm

theorem oddIndependentErasurePorts_label (x : K.Dart) :
    Port.label H.jointLabel (oddIndependentErasurePorts a hi t x) = Port.label K.jointLabel x := by
  cases x with
  | top j => exact j.elim0
  | bottom j => exact j.elim0
  | joint j side => exact isEmptyElim j
  | hub h p =>
    obtain ⟨g, q, hg, hl⟩ := t.portEmbedding_hub_data h p
    have he := t.portLabel (.hub h p)
    rw [hg] at he
    change Port.label H.jointLabel (oddIndependentCutPort a (t.portEmbedding (.hub h p))) = _
    rw [hg]
    exact he

theorem oddIndependentCut_terminal_of_rim (j : WheelCycleIndex)
    (x : (oddIndependentCutGraph a hi).Dart)
    (hx : Port.label (oddIndependentCutGraph a hi).jointLabel x ∈ Set.range (numberedWheelCycles j).edge) :
    (oddIndependentCutGraph a hi).Terminal x := by
  cases x with
  | top i => trivial
  | bottom i => trivial
  | hub h p => trivial
  | joint i side => exact (odd_row_spoke_not_cycle j hx).elim

theorem oddIndependentErasurePorts_twin (j : WheelCycleIndex) (x : K.Dart)
    (hx : Port.label K.jointLabel x ∈ Set.range (numberedWheelCycles j).edge) :
    oddIndependentErasurePorts a hi t (K.pairing.twin x) =
      H.pairing.twin (oddIndependentErasurePorts a hi t x) := by
  have hT := oddIndependentCut_terminal_of_rim a hi j
    ((oddIndependentCutGraph a hi).pairing.twin (t.portEmbedding x)) (by
      rw [(oddIndependentCutGraph a hi).pairing.label_twin, t.portLabel]
      exact hx)
  change oddIndependentCutPort a (t.portEmbedding (K.pairing.twin x)) = _
  rw [t.portEmbedding_twin_of_terminal x hT]
  exact oddIndependentCutGraph_twin a hi (t.portEmbedding x)

theorem oddIndependentErasurePorts_unmarked (x : K.Dart) :
    ¬ (closedSigmaRimCircuit H oddWheelCycle a).Marked (oddIndependentErasurePorts a hi t x) := by
  cases x with
  | top j => exact j.elim0
  | bottom j => exact j.elim0
  | joint j side => exact isEmptyElim j
  | hub h p =>
    obtain ⟨g, q, hg, _⟩ := t.portEmbedding_hub_data h p
    change ¬ (closedSigmaRimCircuit H oddWheelCycle a).Marked
      (oddIndependentCutPort a (t.portEmbedding (.hub h p)))
    rw [hg]
    exact oddIndependentCutPort_hub_unmarked a g q

end ThomGame.Construction
