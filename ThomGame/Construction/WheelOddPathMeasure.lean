module

public import ThomGame.Construction.WheelOddInsertedFace
public import ThomGame.Pictures.RimFacialCoverAt
public import ThomGame.Pictures.RowPairInsertionDisjoint

/-!
# Counting covered-path copies not yet belonging to facial covers

Each actual covered-path component has exactly one hub over its first
row. The measure counts those hubs whose rim is not a facial cover.
It is independent of circuit enumeration and of stellar-cover proofs.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.RowPairInsertion

open scoped Classical

variable {R S : Type*} {A : SparseSystem R S} {G : SolutionGroup.RowGraph A [] []}
  (s : G.RowPairInsertion) (o : Bool) (r : R) (hr : r ≠ s.row)

noncomputable def labelHubEquiv : G.LabelHub r ≃ (s.graph o).LabelHub r :=
  Equiv.ofBijective (fun h => ⟨.inl h.val, h.property⟩) ⟨by
    intro h k he
    exact Subtype.ext (Sum.inl.inj (congrArg Subtype.val he)), by
    rintro ⟨h | b, hh⟩
    · exact ⟨⟨h, hh⟩, rfl⟩
    · exact (hr hh.symm).elim⟩

theorem labelHubEquiv_val (h : G.LabelHub r) : (s.labelHubEquiv o r hr h).val = .inl h.val := rfl

end ThomGame.Pictures.PortGraph.RowPairInsertion

namespace ThomGame.Construction

open Pictures PortGraph
open scoped Classical

variable (H : SigmaGraph [] []) [IsEmpty H.Joint]

noncomputable def oddPathSeedPort (h : H.LabelHub (oddCoveredRowPath.vertex 0)) : H.Dart :=
  H.rowLabelPort (oddCoveredRowPath.vertex 0) (numberedSystem.column (rowEquiv oddRow) 2)
    oddPath_second_cut_incident h

omit [IsEmpty H.Joint] in
theorem oddPathSeedPort_label (h : H.LabelHub (oddCoveredRowPath.vertex 0)) :
    Port.label H.jointLabel (oddPathSeedPort H h) = (numberedWheelCycles oddWheelCycle).edge 1 :=
  (H.rowLabelPort_label _ _ _ _).trans odd_row_column_two

noncomputable def oddPathSeedRim (h : H.LabelHub (oddCoveredRowPath.vertex 0)) :
    H.RimDart (numberedWheelCycles oddWheelCycle) := ⟨oddPathSeedPort H h, ⟨1, (oddPathSeedPort_label H h).symm⟩⟩

omit [IsEmpty H.Joint] in
theorem oddPathSeedRim_onCircuit (h : H.LabelHub (oddCoveredRowPath.vertex 0)) :
    (closedSigmaRimCircuit H oddWheelCycle (oddPathSeedRim H h)).OnCircuitVertex (.inr (.inl h.val)) :=
  ⟨0, congrArg Port.vertex (congrArg Subtype.val
    (OrbitEnumeration.dart_zero (H.rimWalk (numberedWheelCycles oddWheelCycle)
      (numberedWheelCycles oddWheelCycle).empty_boundary_no_rim
      (numberedWheelCycles oddWheelCycle).empty_boundary_no_rim) (oddPathSeedRim H h)))⟩

def OddPathGood (h : H.LabelHub (oddCoveredRowPath.vertex 0)) : Prop :=
  H.RimFacialCoverAt (numberedWheelCycles oddWheelCycle) (oddPathSeedPort H h)

abbrev OddUnfinishedPath := {h : H.LabelHub (oddCoveredRowPath.vertex 0) // ¬ OddPathGood H h}

noncomputable instance oddUnfinishedPathFintype : Fintype (OddUnfinishedPath H) := Fintype.ofFinite _

noncomputable def oddUnfinishedPathCount : Nat := Nat.card (OddUnfinishedPath H)

omit [IsEmpty H.Joint] in
theorem oddUnfinishedPathCount_eq_zero_iff : oddUnfinishedPathCount H = 0 ↔ ∀ h, OddPathGood H h := by
  constructor
  · intro hz h
    by_contra hn
    have hp : 0 < Fintype.card (OddUnfinishedPath H) := Fintype.card_pos_iff.mpr ⟨⟨h, hn⟩⟩
    rw [oddUnfinishedPathCount, Nat.card_eq_fintype_card] at hz
    omega
  · intro hg
    have hi : IsEmpty (OddUnfinishedPath H) := ⟨fun h => h.property (hg h.val)⟩
    let := hi
    simp [oddUnfinishedPathCount]

variable {H}
  (hf : ∀ i : WheelCycleIndex, i ≠ oddWheelCycle → SigmaRimsFacialCovers H i)
  (h : H.LabelHub (oddCoveredRowPath.vertex 0))

include hf h in
theorem oddPath_seed_row_ne_oddRow : oddCoveredRowPath.vertex 0 ≠ rowEquiv oddRow := by
  intro he
  have h1 := oddInsertedHub_label hf h (1 : Fin 5)
  have h0 := oddInsertedHub_label hf h (0 : Fin 5)
  have hm : (oddPathInsertion hf h).hubLabel (oddInsertedHub hf h 1) =
      (oddPathInsertion hf h).hubLabel (oddInsertedHub hf h 0) := h.property.trans he
  have hi := (numberedWheelCycles oddWheelCycle).vertex.injective (h1.symm.trans (hm.trans h0))
  exact (by decide +kernel : (1 : Fin 5) ≠ 0) hi

theorem oddPathInsertion_second_eq_seed : (oddPathInsertion hf h).second = oddPathSeedPort H h := rfl

noncomputable def oddInsertedSeedEquiv (o : Bool) :
    H.LabelHub (oddCoveredRowPath.vertex 0) ≃ (oddPathInsertedGraph hf h o).LabelHub (oddCoveredRowPath.vertex 0) :=
  (oddPathInsertion hf h).labelHubEquiv o (oddCoveredRowPath.vertex 0) (oddPath_seed_row_ne_oddRow hf h)

theorem oddInsertedSeedPort (o : Bool) (k : H.LabelHub (oddCoveredRowPath.vertex 0)) :
    oddPathSeedPort (oddPathInsertedGraph hf h o) (oddInsertedSeedEquiv hf h o k) =
      (oddPathInsertion hf h).old (oddPathSeedPort H k) := rfl

end ThomGame.Construction
