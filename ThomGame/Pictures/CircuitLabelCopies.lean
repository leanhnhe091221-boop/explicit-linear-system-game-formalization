module

public import ThomGame.Pictures.CircuitCoverProjection
public import ThomGame.Pictures.PermutationCoverFibers

/-!
# Covering degree, actual labelled copies, and repeated prescribed edges

For a labelled rim cover, every base edge has the same positive number
of preimages and the circuit length is the base length times this degree.
A cover without repeated edge labels is a genuine copy: explicit edge
and vertex bijections preserve all original labels. Every noncopy cover
contains two distinct actual edges over any prescribed base edge.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open Equiv
open scoped Classical

variable {R S : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
  {G : SolutionGroup.RowGraph A [] []} [IsEmpty G.Joint]
  (C : G.SimpleCircuit) (γ : Hypergraph.Cycle A.hypergraph)
  (hl : ∀ i : Fin C.length, Port.label G.jointLabel (C.dart i) ∈ Set.range γ.edge)
  (hc : C.IsLabelCover)

def IsLabelCopy : Prop :=
  C.IsLabelCover ∧ Function.Injective (fun i : Fin C.length => Port.label G.jointLabel (C.dart i))

noncomputable def coverDegree : Nat := Fintype.card {i : Fin C.length // C.coverEdgeIndex γ hl i = 0}

include hc in
theorem coverEdgeIndex_surjective : Function.Surjective (C.coverEdgeIndex γ hl) := by
  rcases C.coverEdgeIndex_semiconj γ hl hc with hf | hb
  · exact PermutationCover.surjective _ _ _ hf (fun i j => finRotate_sameCycle i j) 0
  · exact PermutationCover.surjective _ _ _ hb (fun i j => (finRotate_sameCycle i j).inv) 0

include hc in
theorem coverDegree_pos : 0 < C.coverDegree γ hl := by
  obtain ⟨i, hi⟩ := C.coverEdgeIndex_surjective γ hl hc 0
  exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩

include hc in
theorem coverEdgeIndex_fiber_card (j : Fin γ.length) :
    Fintype.card {i : Fin C.length // C.coverEdgeIndex γ hl i = j} = C.coverDegree γ hl := by
  rcases C.coverEdgeIndex_semiconj γ hl hc with hf | hb
  · simpa only [coverDegree, ← Nat.card_eq_fintype_card] using PermutationCover.fiber_card _ _ _ hf (fun i j => finRotate_sameCycle i j) j 0
  · simpa only [coverDegree, ← Nat.card_eq_fintype_card] using PermutationCover.fiber_card _ _ _ hb (fun i j => (finRotate_sameCycle i j).inv) j 0

include hc in
theorem cover_length_eq : C.length = γ.length * C.coverDegree γ hl := by
  rcases C.coverEdgeIndex_semiconj γ hl hc with hf | hb
  · simpa only [coverDegree, ← Nat.card_eq_fintype_card, Nat.card_fin] using
      PermutationCover.card_eq_mul_fiber _ _ _ hf (fun i j => finRotate_sameCycle i j) (0 : Fin γ.length)
  · simpa only [coverDegree, ← Nat.card_eq_fintype_card, Nat.card_fin] using
      PermutationCover.card_eq_mul_fiber _ _ _ hb (fun i j => (finRotate_sameCycle i j).inv) (0 : Fin γ.length)

include hc in
theorem coverVertexIndex_surjective : Function.Surjective (C.coverVertexIndex γ hl) := by
  intro j
  obtain ⟨i, hi⟩ := C.coverEdgeIndex_surjective γ hl hc j
  rcases C.coverEdgeIndex_source γ hl i with hb | hf
  · exact ⟨i, hb.symm.trans hi⟩
  · exact ⟨finRotate C.length i, (C.cover_step_forward γ hl hc i hf).1.trans hi⟩

omit [IsEmpty G.Joint] in
theorem coverEdgeIndex_injective_iff : Function.Injective (C.coverEdgeIndex γ hl) ↔
    Function.Injective (fun i : Fin C.length => Port.label G.jointLabel (C.dart i)) := by
  constructor
  · intro he i j hij
    exact he (γ.edge.injective ((C.coverEdgeIndex_label γ hl i).trans
      (hij.trans (C.coverEdgeIndex_label γ hl j).symm)))
  · intro he i j hij
    exact he ((C.coverEdgeIndex_label γ hl i).symm.trans
      ((congrArg γ.edge hij).trans (C.coverEdgeIndex_label γ hl j)))

include hl hc in
theorem isLabelCopy_iff_length : C.IsLabelCopy ↔ C.length = γ.length := by
  constructor
  · intro hcopy
    have hb : Function.Bijective (C.coverEdgeIndex γ hl) :=
      ⟨(C.coverEdgeIndex_injective_iff γ hl).mpr hcopy.2, C.coverEdgeIndex_surjective γ hl hc⟩
    simpa only [Fintype.card_fin] using Fintype.card_of_bijective hb
  · intro he
    have hcard : Fintype.card (Fin C.length) = Fintype.card (Fin γ.length) := by simpa using he
    have hb := (Fintype.bijective_iff_surjective_and_card (C.coverEdgeIndex γ hl)).mpr
      ⟨C.coverEdgeIndex_surjective γ hl hc, hcard⟩
    exact ⟨hc, (C.coverEdgeIndex_injective_iff γ hl).mp hb.1⟩

variable (hcopy : C.IsLabelCopy)

noncomputable def copyEdgeEquiv : Fin C.length ≃ Fin γ.length :=
  Equiv.ofBijective (C.coverEdgeIndex γ hl)
    ⟨(C.coverEdgeIndex_injective_iff γ hl).mpr hcopy.2, C.coverEdgeIndex_surjective γ hl hcopy.1⟩

theorem copyEdgeEquiv_label (i : Fin C.length) :
    γ.edge (C.copyEdgeEquiv γ hl hcopy i) = Port.label G.jointLabel (C.dart i) :=
  C.coverEdgeIndex_label γ hl i

noncomputable def copyVertexEquiv : Fin C.length ≃ Fin γ.length :=
  Equiv.ofBijective (C.coverVertexIndex γ hl)
    ((Fintype.bijective_iff_surjective_and_card _).mpr
      ⟨C.coverVertexIndex_surjective γ hl hcopy.1, Fintype.card_congr (C.copyEdgeEquiv γ hl hcopy)⟩)

theorem copyVertexEquiv_label (i : Fin C.length) :
    γ.vertex (C.copyVertexEquiv γ hl hcopy i) = G.hubLabel (C.hubAt i) := C.coverVertexIndex_label γ hl i

include hl hc in
theorem noncopy_repeats_every_edge (hn : ¬ C.IsLabelCopy) (j : Fin γ.length) :
    ∃ i k : Fin C.length, i ≠ k ∧
      Port.label G.jointLabel (C.dart i) = γ.edge j ∧
      Port.label G.jointLabel (C.dart k) = γ.edge j ∧
      G.pairing.edge (C.dart i) ≠ G.pairing.edge (C.dart k) := by
  have hni : ¬ Function.Injective (C.coverEdgeIndex γ hl) :=
    fun he => hn ⟨hc, (C.coverEdgeIndex_injective_iff γ hl).mp he⟩
  have hex : ∃ i k : Fin C.length, i ≠ k ∧ C.coverEdgeIndex γ hl i = j ∧ C.coverEdgeIndex γ hl k = j := by
    rcases C.coverEdgeIndex_semiconj γ hl hc with hf | hb
    · exact PermutationCover.repeated_over_every_target _ _ _ hf (fun i j => finRotate_sameCycle i j) hni j
    · exact PermutationCover.repeated_over_every_target _ _ _ hb (fun i j => (finRotate_sameCycle i j).inv) hni j
  obtain ⟨i, k, hne, hi, hk⟩ := hex
  exact ⟨i, k, hne, (C.coverEdgeIndex_label γ hl i).symm.trans (congrArg γ.edge hi),
    (C.coverEdgeIndex_label γ hl k).symm.trans (congrArg γ.edge hk), fun he => hne (C.edge_injective he)⟩

end ThomGame.Pictures.PortGraph.SimpleCircuit
