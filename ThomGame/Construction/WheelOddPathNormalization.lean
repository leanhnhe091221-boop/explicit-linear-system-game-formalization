module

public import ThomGame.Construction.WheelOddInsertionDescent
public import ThomGame.Construction.WheelOddPathTerminal

/-!
# Finite exceptional-path normalization by actual Figure 19(b) insertions

Strong induction on the unfinished-path count repeatedly applies the
proved strict decrease to the actual output graph. The final graph is
character-equivalent and Euler-saturated. All stellar facial covers
survive, and every exceptional rim is a facial cover or uses only
independent labels. Size need not be minimal and grows by at most twice
the original unfinished-path count.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures PortGraph RibbonConnectivity
open scoped Classical

variable {H : SigmaGraph [] []} [IsEmpty H.Joint]

theorem exists_odd_path_normalization
    (hEuler : eulerDefect H.pairing.perm H.circuitStep = 0)
    (hf : ∀ i : WheelCycleIndex, i ≠ oddWheelCycle → SigmaRimsFacialCovers H i) :
    ∃ K : SigmaGraph [] [], IsEmpty K.Joint ∧
      eulerDefect K.pairing.perm K.circuitStep = 0 ∧ K.character = H.character ∧ K.sign = H.sign ∧
      (∀ i : WheelCycleIndex, i ≠ oddWheelCycle → SigmaRimsFacialCovers K i) ∧
      (∀ h : K.LabelHub (oddCoveredRowPath.vertex 0), OddPathGood K h) ∧
      Fintype.card K.Hub ≤ Fintype.card H.Hub + 2 * oddUnfinishedPathCount H := by
  generalize hn : oddUnfinishedPathCount H = n
  induction n using Nat.strong_induction_on generalizing H with
  | h n ih =>
    by_cases hg : ∀ h : H.LabelHub (oddCoveredRowPath.vertex 0), OddPathGood H h
    · exact ⟨H, inferInstance, hEuler, rfl, rfl, hf, hg, by omega⟩
    · obtain ⟨h, hbad⟩ := not_forall.mp hg
      obtain ⟨o, he, hchar, hlt, hfaces⟩ := oddPathInsertion_exists_decreasing hf h hbad hEuler
      let G := oddPathInsertedGraph hf h o
      have hGn : oddUnfinishedPathCount G < n := by simpa only [hn] using hlt
      obtain ⟨K, hKJ, hKe, hKc, hKs, hKf, hKg, hKb⟩ :=
        ih (oddUnfinishedPathCount G) hGn he hfaces rfl
      refine ⟨K, hKJ, hKe, hKc.trans hchar,
        hKs.trans (oddPathInsertedGraph_sign hf h o), hKf, hKg, ?_⟩
      calc
        Fintype.card K.Hub ≤ Fintype.card G.Hub + 2 * oddUnfinishedPathCount G := hKb
        _ = Fintype.card H.Hub + 2 + 2 * oddUnfinishedPathCount G :=
          congrArg (fun m => m + 2 * oddUnfinishedPathCount G) (oddPathInsertedGraph_hub_card hf h o)
        _ ≤ Fintype.card H.Hub + 2 * n := by omega

/-- The exceptional part of the paper's intermediate picture P₂:
all non-independent portions are contained in actual facial covers. -/
theorem exists_odd_rim_normalization
    (hEuler : eulerDefect H.pairing.perm H.circuitStep = 0)
    (hf : ∀ i : WheelCycleIndex, i ≠ oddWheelCycle → SigmaRimsFacialCovers H i) :
    ∃ K : SigmaGraph [] [], IsEmpty K.Joint ∧
      eulerDefect K.pairing.perm K.circuitStep = 0 ∧ K.character = H.character ∧ K.sign = H.sign ∧
      (∀ i : WheelCycleIndex, i ≠ oddWheelCycle → SigmaRimsFacialCovers K i) ∧
      (∀ a : K.RimDart (numberedWheelCycles oddWheelCycle),
        ((∃ side, (closedSigmaRimCircuit K oddWheelCycle a).BoundsFaceOrbit side) ∧
          (closedSigmaRimCircuit K oddWheelCycle a).IsLabelCover) ∨ OddRimIndependentOnly K a) ∧
      Fintype.card K.Hub ≤ Fintype.card H.Hub + 2 * oddUnfinishedPathCount H := by
  obtain ⟨K, hKJ, he, hc, hs, hfK, hg, hb⟩ := exists_odd_path_normalization hEuler hf
  let : IsEmpty K.Joint := hKJ
  exact ⟨K, hKJ, he, hc, hs, hfK,
    fun a => oddRim_facial_cover_or_independent hfK a he hg, hb⟩

end ThomGame.Construction
