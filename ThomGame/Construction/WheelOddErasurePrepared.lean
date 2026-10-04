module

public import ThomGame.Construction.WheelOddErasureCircuits

/-!
# Independent-rim erasure stays in the prepared character class

Every final canonical rim recovers to an actual original labelled
simple circuit. Original facial covers reflect back to final facial
covers. An original independent-only rim retains its two labels.
Thus the actual erased and smoothed graph satisfies all rim conditions
required by the new character-class minimum.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures PortGraph RibbonConnectivity
open scoped Classical

theorem closedSigmaRimCircuit_base_marked (G : SigmaGraph [] []) (j : WheelCycleIndex)
    (x : G.RimDart (numberedWheelCycles j)) : (closedSigmaRimCircuit G j x).Marked x.val :=
  ⟨(0, false), congrArg Subtype.val (OrbitEnumeration.dart_zero
    (G.rimWalk (numberedWheelCycles j) (by simp) (by simp)) x)⟩

theorem sigmaCircuit_facial_cover_of_base {G : SigmaGraph [] []}
    (hEuler : eulerDefect G.pairing.perm G.circuitStep = 0)
    (j : WheelCycleIndex) (D : G.SimpleCircuit)
    (hl : ∀ i : Fin D.length, Port.label G.jointLabel (D.dart i) ∈ Set.range (numberedWheelCycles j).edge)
    (x : G.RimDart (numberedWheelCycles j)) (hx : D.Marked x.val)
    (hf : (∃ side, (closedSigmaRimCircuit G j x).BoundsFaceOrbit side) ∧
      (closedSigmaRimCircuit G j x).IsLabelCover) :
    (∃ side, D.BoundsFaceOrbit side) ∧ D.IsLabelCover := by
  apply (G.rimFacialCoverAt_iff_circuit (by simp) (by simp) D hl
    (G.dualEuler_eq_twice_components hEuler) hx).mp
  exact ⟨closedSigmaRimCircuit G j x,
    G.rimSimpleCircuit_rim (numberedWheelCycles j) (by simp) (by simp) x,
    hf.1, hf.2, closedSigmaRimCircuit_base_marked G j x⟩

variable {H : SigmaGraph [] []} [IsEmpty H.Joint]
  (a : H.RimDart (numberedWheelCycles oddWheelCycle)) (hi : OddRimIndependentOnly H a)
  {K : SigmaGraph [] []} {circles : List (Fin 1889684)}
  (t : Smoothing (oddIndependentCutGraph a hi) K circles) [IsEmpty K.Joint]

include t in
theorem oddIndependentErasure_stellar
    (hEuler : eulerDefect H.pairing.perm H.circuitStep = 0)
    (j : WheelCycleIndex) (hf : SigmaRimsFacialCovers H j) : SigmaRimsFacialCovers K j := by
  intro b
  let D := closedSigmaRimCircuit K j b
  have hl : ∀ i : Fin D.length, Port.label K.jointLabel (D.dart i) ∈ Set.range (numberedWheelCycles j).edge :=
    K.rimSimpleCircuit_rim (numberedWheelCycles j) (by simp) (by simp) b
  let L := oddErasureRecoveredCircuit a hi t j D hl
  have hL := oddErasureRecoveredCircuit_rim a hi t j D hl
  let x : H.RimDart (numberedWheelCycles j) := ⟨L.dart 0, hL 0⟩
  obtain ⟨⟨side, hs⟩, hc⟩ := sigmaCircuit_facial_cover_of_base hEuler j L hL x ⟨(0, false), rfl⟩ (hf x)
  exact ⟨⟨side, oddErasureRecoveredCircuit_face a hi t j D hl side hs⟩,
    oddErasureRecoveredCircuit_cover a hi t j D hl hc⟩

include t in
theorem oddIndependentErasure_prepared
    (hEuler : eulerDefect H.pairing.perm H.circuitStep = 0)
    (hp : SigmaRimPrepared H) : SigmaRimPrepared K := by
  refine ⟨fun j hj => oddIndependentErasure_stellar a hi t hEuler j (hp.1 j hj), ?_⟩
  intro b
  let D := closedSigmaRimCircuit K oddWheelCycle b
  have hl : ∀ i : Fin D.length,
      Port.label K.jointLabel (D.dart i) ∈ Set.range (numberedWheelCycles oddWheelCycle).edge :=
    K.rimSimpleCircuit_rim (numberedWheelCycles oddWheelCycle) (by simp) (by simp) b
  let L := oddErasureRecoveredCircuit a hi t oddWheelCycle D hl
  have hL := oddErasureRecoveredCircuit_rim a hi t oddWheelCycle D hl
  let x : H.RimDart (numberedWheelCycles oddWheelCycle) := ⟨L.dart 0, hL 0⟩
  rcases hp.2 x with hf | hx
  · obtain ⟨⟨side, hs⟩, hc⟩ := sigmaCircuit_facial_cover_of_base hEuler oddWheelCycle L hL x
      ⟨(0, false), rfl⟩ hf
    exact Or.inl ⟨⟨side, oddErasureRecoveredCircuit_face a hi t oddWheelCycle D hl side hs⟩,
      oddErasureRecoveredCircuit_cover a hi t oddWheelCycle D hl hc⟩
  · apply Or.inr
    intro i
    have he := L.marked_iff_of_common_rim_port (numberedWheelCycles oddWheelCycle) (by simp) (by simp)
      hL (closedSigmaRimCircuit H oddWheelCycle x)
      (H.rimSimpleCircuit_rim (numberedWheelCycles oddWheelCycle) (by simp) (by simp) x)
      x.val ⟨(0, false), rfl⟩ (closedSigmaRimCircuit_base_marked H oddWheelCycle x)
    have hmark := (he (L.dart i)).mp ⟨(i, false), rfl⟩
    have hind := oddIndependent_marked_labels x hx hmark
    change Port.label H.jointLabel ((oddErasureRecoveredCircuit a hi t oddWheelCycle D hl).dart i) = _ ∨
      Port.label H.jointLabel ((oddErasureRecoveredCircuit a hi t oddWheelCycle D hl).dart i) = _ at hind
    rw [oddErasureRecoveredCircuit_label] at hind
    rcases hind with hind | hind
    · exact ⟨0, by decide +kernel, hind.symm⟩
    · exact ⟨1, by decide +kernel, hind.symm⟩

end ThomGame.Construction
