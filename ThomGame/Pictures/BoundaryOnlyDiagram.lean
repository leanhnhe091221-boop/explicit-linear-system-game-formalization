module

public import ThomGame.Pictures.MatchingDiagram
public import ThomGame.Pictures.BoundaryOrderSmoothing

/-!
# The boundary-only case of graph realization

A graph without relation hubs has a vertex-free diagram with the same
ordered boundary whenever its boundary matching is noncrossing. Arbitrary
subdivision joints are removed by a genuine smoothing trace first.
This proves boundary and relation-list realization, not a graph isomorphism.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open CircularPartition

variable {R S : Type*} {P : InvolutionPresentation R S} {w : List S}

section Reduced

variable (G : PortGraph P w []) [IsEmpty G.Hub] [IsEmpty G.Joint]

def topOnlyPorts : Fin w.length ≃ G.Dart where
  toFun i := .top i
  invFun
    | .top i => i
    | .bottom i => i.elim0
    | .hub h _ => isEmptyElim h
    | .joint j _ => isEmptyElim j
  left_inv _ := rfl
  right_inv a := by
    cases a with
    | top i => rfl
    | bottom i => exact i.elim0
    | hub h _ => exact (isEmptyElim h : False).elim
    | joint j _ => exact (isEmptyElim j : False).elim

def topOnlyPairing : Pairing (fun i : Fin w.length => w[i]) :=
  G.pairing.transport G.topOnlyPorts.symm _ (by
    intro a
    cases a with
    | top i => rfl
    | bottom i => exact i.elim0
    | hub h _ => exact (isEmptyElim h : False).elim
    | joint j _ => exact (isEmptyElim j : False).elim)

theorem topOnlyPairing_twin (i : Fin w.length) :
    G.pairing.twin (.top i) = .top (G.topOnlyPairing.twin i) :=
  (G.topOnlyPorts.apply_symm_apply _).symm

theorem boundaryNext_topOnly (i : Fin w.length) :
    G.boundaryNext (.inl i) = .inl (G.topOnlyPairing.twin i) := by
  apply G.boundaryNext_eq_of_step
  change G.rotation (G.pairing.twin (.top i)) = .top (G.topOnlyPairing.twin i)
  rw [G.topOnlyPairing_twin]
  rfl

theorem topOnlyPairing_noninterlacing (hnc : G.BoundaryNoncrossing) :
    NonInterlacing sbtw G.topOnlyPairing.perm := by
  let e : Fin w.length ↪ BoundaryIndex w [] := Function.Embedding.inl
  have he : FiniteReturn.Advances G.boundaryNext G.topOnlyPairing.perm e :=
    fun i => Or.inl (G.boundaryNext_topOnly i).symm
  intro a b c d habc hacd hac hbd
  apply (he.sameCycle_iff a b).mpr
  apply hnc.noninterlacing (.inl a) (.inl b) (.inl c) (.inl d)
  · simpa only [boundaryBetween, Fin.sbtw_iff, Fin.lt_def, boundaryOrderIndex_top_val] using habc
  · simpa only [boundaryBetween, Fin.sbtw_iff, Fin.lt_def, boundaryOrderIndex_top_val] using hacd
  · exact (he.sameCycle_iff a c).mp hac
  · exact (he.sameCycle_iff b d).mp hbd

theorem exists_diagram_of_boundary_only (hnc : G.BoundaryNoncrossing) :
    ∃ d : Diagram P w [], d.labels = [] :=
  exists_matching_word_diagram P w G.topOnlyPairing (G.topOnlyPairing_noninterlacing hnc)

end Reduced

theorem exists_diagram_of_no_hubs (G : PortGraph P w []) [IsEmpty G.Hub]
    (hnc : G.BoundaryNoncrossing) : ∃ d : Diagram P w [], d.labels = [] := by
  obtain ⟨H, circles, ⟨t⟩, hJ⟩ := Smoothing.exists_without_junctions G
  let : IsEmpty H.Joint := hJ
  let : IsEmpty H.Hub := ⟨fun h => isEmptyElim (t.hubEquiv.symm h)⟩
  exact H.exists_diagram_of_boundary_only (t.boundaryNoncrossing_iff.mpr hnc)

end ThomGame.Pictures.PortGraph
