module

public import ThomGame.Construction.WheelRimMaximum
public import ThomGame.Pictures.CircuitCopySwitch

/-!
# Prescribed repeated-edge switches in the actual maximal Sigma graph

The copy predicate is certified by bijections of the actual edge and
hub labels. If a canonical rim of the maximal facial-cover graph is
not a copy, any selected base edge supplies two distinct cuts and an
actual same-row reconnection graph. Its remaining Euler, new-face and
strict rim-count properties must still be established.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures PortGraph

def SigmaRimsFacialCopies (H : SigmaGraph [] []) (j : WheelCycleIndex) : Prop :=
  ∀ a : H.RimDart (numberedWheelCycles j),
    (∃ side, (closedSigmaRimCircuit H j a).BoundsFaceOrbit side) ∧
      (closedSigmaRimCircuit H j a).IsLabelCopy

theorem numbered_hasPrivateEdge {j : WheelCycleIndex} (h : Hypergraph.HasPrivateEdge wheelCycles j) :
    Hypergraph.HasPrivateEdge numberedWheelCycles j := by
  obtain ⟨e, he, hu⟩ := h
  refine ⟨colEquiv e, (numberedWheelCycles_edge_range j _).mpr ?_, ?_⟩
  · simpa only [Equiv.symm_apply_apply] using he
  · intro k hk
    apply hu k
    simpa only [Equiv.symm_apply_apply] using (numberedWheelCycles_edge_range k _).mp hk

theorem numbered_pentagon_private_edge (r : WheelIndex) (j : Fin (wheelFamily.size r)) :
    Hypergraph.HasPrivateEdge numberedWheelCycles (.inr ⟨r, j⟩) :=
  numbered_hasPrivateEdge (pentagon_private_edge r j)

namespace SigmaMaximalRimState

variable {H : SigmaGraph [] []} [IsEmpty H.Joint] (h : SigmaMaximalRimState H)

include h in
theorem noncopy_facial_switch (j : WheelCycleIndex) (a : H.RimDart (numberedWheelCycles j))
    (hn : ¬ (closedSigmaRimCircuit H j a).IsLabelCopy) (k : Fin (numberedWheelCycles j).length) :
    ∃ s : H.RowEdgeSwitch,
      (closedSigmaRimCircuit H j a).Marked s.first ∧ (closedSigmaRimCircuit H j a).Marked s.second ∧
      Port.label H.jointLabel s.first = (numberedWheelCycles j).edge k ∧
      (H.circuitStep.SameCycle s.first s.second ∨
        H.circuitStep.SameCycle (H.pairing.twin s.first) (H.pairing.twin s.second)) :=
  (closedSigmaRimCircuit H j a).exists_noncopy_facial_switch (numberedWheelCycles j)
    (H.rimSimpleCircuit_rim (numberedWheelCycles j) (by simp) (by simp) a)
    (h.covers j a).2 hn (h.covers j a).1 k

include h in
theorem private_noncopy_switch (j : WheelCycleIndex) (hp : Hypergraph.HasPrivateEdge numberedWheelCycles j)
    (a : H.RimDart (numberedWheelCycles j)) (hn : ¬ (closedSigmaRimCircuit H j a).IsLabelCopy) :
    ∃ s : H.RowEdgeSwitch,
      (closedSigmaRimCircuit H j a).Marked s.first ∧ (closedSigmaRimCircuit H j a).Marked s.second ∧
      (H.circuitStep.SameCycle s.first s.second ∨
        H.circuitStep.SameCycle (H.pairing.twin s.first) (H.pairing.twin s.second)) ∧
      ∀ k : WheelCycleIndex, k ≠ j → Port.label H.jointLabel s.first ∉ Set.range (numberedWheelCycles k).edge := by
  obtain ⟨e, ⟨i, hi⟩, hprivate⟩ := hp
  obtain ⟨s, hs, ht, hlabel, hf⟩ := h.noncopy_facial_switch j a hn i
  refine ⟨s, hs, ht, hf, ?_⟩
  intro k hk he
  exact hk (hprivate k ((hlabel.trans hi) ▸ he))

end SigmaMaximalRimState
end ThomGame.Construction
