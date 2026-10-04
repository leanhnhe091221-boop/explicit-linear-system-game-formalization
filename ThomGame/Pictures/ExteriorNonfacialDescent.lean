module

public import ThomGame.Pictures.RimNonfacialCount
public import ThomGame.Pictures.ExteriorPreimageInjectivity

/-!
# Strict descent of nonfacial rim components under region replacement

If every nonfacial target circuit comes from the complementary region,
its recovered original component is nonfacial. Recovery is injective on
components, and its image omits the selected nonfacial circuit. The
result is strict descent of the finite component count, rather than a
count of indexed circuit enumerations.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open RibbonConnectivity

variable {R S : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
  {G : SolutionGroup.RowGraph A [] []} (γ : Hypergraph.Cycle A.hypergraph) (B : G.SimpleCircuit)
  (hB : ∀ k : Fin B.length, Port.label G.jointLabel (B.dart k) ∈ Set.range γ.edge)
  (hNonface : ¬ ∃ side, B.BoundsFaceOrbit side)
  (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
    2 * Nat.card (Component G.circuitStep G.pairing.perm)) (s : Bool)
  {N : SolutionGroup.RowGraph A (B.frontierWord s) []}
  (d : ThomGame.Pictures.ClosedGluingReduction (B.regionGraph hEuler s).swapBoundary N)
  (hTargetEuler : RotationEuler.count d.graph.circuitStep d.graph.pairing.perm =
    2 * Nat.card (Component d.graph.circuitStep d.graph.pairing.perm))
  (hpre : ∀ C : d.graph.SimpleCircuit,
    (∀ k : Fin C.length, Port.label d.graph.jointLabel (C.dart k) ∈ Set.range γ.edge) →
      (¬ ∃ side, C.BoundsFaceOrbit side) → d.HasLeftPreimage C)

include hB hNonface hTargetEuler hpre in
theorem nonfacialRimCount_lt_of_exterior_preimages :
    d.graph.nonfacialRimCount γ (by simp) (by simp) < G.nonfacialRimCount γ (by simp) (by simp) := by
  classical
  let X := d.graph.nonfacialRimCircuit γ (by simp) (by simp)
  have hXlabels (c : d.graph.NonfacialRimComponent γ (by simp) (by simp))
      (k : Fin (X c).length) : Port.label d.graph.jointLabel ((X c).dart k) ∈ Set.range γ.edge :=
    d.graph.nonfacialRimCircuit_labels γ (by simp) (by simp) c k
  have hXnonface (c : d.graph.NonfacialRimComponent γ (by simp) (by simp)) :
      ¬ ∃ side, (X c).BoundsFaceOrbit side :=
    d.graph.nonfacialRimCircuit_not_face γ (by simp) (by simp) hTargetEuler c
  have hp : ∀ c : d.graph.NonfacialRimComponent γ (by simp) (by simp), d.HasLeftPreimage (X c) :=
    fun c => hpre (X c) (hXlabels c) (hXnonface c)
  simp only [ThomGame.Pictures.ClosedGluingReduction.HasLeftPreimage] at hp
  choose D hlen hports using hp
  let O (c : d.graph.NonfacialRimComponent γ (by simp) (by simp)) :=
    B.recoverSwappedRegionCircuit hEuler s (D c)
  have hOlabels (c : d.graph.NonfacialRimComponent γ (by simp) (by simp))
      (k : Fin (O c).length) : Port.label G.jointLabel ((O c).dart k) ∈ Set.range γ.edge := by
    change Port.label G.jointLabel ((B.recoverSwappedRegionCircuit hEuler s (D c)).port (k, false)) ∈ _
    rw [B.recoveredExteriorPreimage_label hEuler s d (X c) (D c) (hlen c) (hports c)]
    exact hXlabels c _
  have hOnonface (c : d.graph.NonfacialRimComponent γ (by simp) (by simp)) :
      ¬ ∃ side, (O c).BoundsFaceOrbit side :=
    B.recoveredExteriorPreimage_nonfacial hEuler s d (X c) (D c) (hlen c) (hports c) (hXnonface c)
  let f : d.graph.NonfacialRimComponent γ (by simp) (by simp) →
      G.NonfacialRimComponent γ (by simp) (by simp) := fun c =>
    ⟨G.rimComponent γ (by simp) (by simp) ((O c).labelledRimDart γ (hOlabels c) 0),
      fun hf => hOnonface c ((G.rimComponentFacial_iff_circuit γ (by simp) (by simp) hEuler
        (O c) (hOlabels c)).mp hf)⟩
  have hfi : Function.Injective f := by
    intro c e he
    have hcomp : G.rimComponent γ (by simp) (by simp) ((O c).labelledRimDart γ (hOlabels c) 0) =
        G.rimComponent γ (by simp) (by simp) ((O e).labelledRimDart γ (hOlabels e) 0) :=
      congrArg Subtype.val he
    have hcommon : (O e).Marked ((O c).dart 0) :=
      ((O e).marked_iff_rimComponent γ (by simp) (by simp) (hOlabels e)
        ((O c).labelledRimDart γ (hOlabels c) 0)).mpr hcomp
    have hm := (O c).marked_iff_of_common_rim_port γ (by simp) (by simp) (hOlabels c)
      (O e) (hOlabels e) ((O c).dart 0) ⟨(0, false), rfl⟩ hcommon
    exact d.graph.nonfacialRimComponent_ext γ (by simp) (by simp) c e
      (B.marked_iff_of_recovered_exterior hEuler s d (X c) (X e) (D c) (D e)
        (hlen c) (hlen e) (hports c) (hports e) hm)
  let selected : G.NonfacialRimComponent γ (by simp) (by simp) :=
    ⟨G.rimComponent γ (by simp) (by simp) (B.labelledRimDart γ hB 0),
      fun hf => hNonface ((G.rimComponentFacial_iff_circuit γ (by simp) (by simp) hEuler B hB).mp hf)⟩
  have hmiss : selected ∉ Set.range f := by
    rintro ⟨c, hc⟩
    have hcomp : G.rimComponent γ (by simp) (by simp) ((O c).labelledRimDart γ (hOlabels c) 0) =
        G.rimComponent γ (by simp) (by simp) (B.labelledRimDart γ hB 0) := congrArg Subtype.val hc
    have hm : (O c).Marked (B.dart 0) :=
      ((O c).marked_iff_rimComponent γ (by simp) (by simp) (hOlabels c)
        (B.labelledRimDart γ hB 0)).mpr hcomp.symm
    obtain ⟨x, hx⟩ := hm
    have hout := B.recoverSwappedRegionCircuit_not_germ hEuler s (D c) x
    change ¬ B.GermVertex (!s) ((O c).port x).vertex at hout
    rw [hx] at hout
    exact hout (Or.inl (B.marked_onCircuitVertex ⟨(0, false), rfl⟩))
  simpa only [PortGraph.nonfacialRimCount, Nat.card_eq_fintype_card] using
    Fintype.card_lt_of_injective_of_notMem f hfi hmiss

end ThomGame.Pictures.PortGraph.SimpleCircuit
