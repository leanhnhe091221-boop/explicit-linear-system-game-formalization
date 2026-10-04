module

public import ThomGame.Pictures.RowGraphEmbedding
public import ThomGame.Pictures.BottomGraphRealization

/-!
# Boundary and Euler invariants of the actual row embedding

The boundary reindexing preserves each numbered occurrence and its circular
order. The full port bijection transports connectivity and face orbits,
so the boundary successor, boundary component condition, and Euler defect
are retained. These statements apply to disconnected graphs as well.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv RibbonConnectivity
open scoped BigOperators

variable {S U : Type*} (f : S → U) (u v : List S)

def mapBoundaryIndex : BoundaryIndex u v ≃ BoundaryIndex (u.map f) (v.map f) :=
  Equiv.sumCongr (mapWordIndex f u) (mapWordIndex f v)

theorem mapBoundaryIndex_order (i : BoundaryIndex u v) :
    boundaryOrderIndex (u.map f) (v.map f) (mapBoundaryIndex f u v i) =
      finCongr (by simp only [List.length_map]) (boundaryOrderIndex u v i) := by
  apply Fin.ext
  cases i with
  | inl i => rfl
  | inr i => simp [mapBoundaryIndex, mapWordIndex, boundaryOrderIndex_bottom_val]

theorem mapBoundaryIndex_cyclic (i : BoundaryIndex u v) :
    boundaryCyclic (u.map f) (v.map f) (mapBoundaryIndex f u v i) =
      mapBoundaryIndex f u v (boundaryCyclic u v i) := by
  apply (boundaryOrderIndex (u.map f) (v.map f)).injective
  rw [boundaryCyclic_index, mapBoundaryIndex_order, mapBoundaryIndex_order, boundaryCyclic_index]
  have h {m n : Nat} (he : m = n) (j : Fin m) :
      finRotate n (finCongr he j) = finCongr he (finRotate m j) := by subst n; rfl
  exact h _ _

theorem mapBoundaryIndex_between (a b c : BoundaryIndex u v) :
    boundaryBetween (u.map f) (v.map f) (mapBoundaryIndex f u v a)
      (mapBoundaryIndex f u v b) (mapBoundaryIndex f u v c) ↔ boundaryBetween u v a b c := by
  simp only [boundaryBetween, mapBoundaryIndex_order, Fin.sbtw_iff]
  rfl

variable {R T : Type*} {A : SparseSystem R S} {B : SparseSystem T U}
  {u v : List S} (G : SolutionGroup.RowGraph A u v)
  (ι : A.hypergraph.OpenEmbedding B.hypergraph)

theorem rowEmbeddingPorts_vertex_iff (a b : G.Dart) :
    (G.rowEmbeddingPorts ι a).vertex = (G.rowEmbeddingPorts ι b).vertex ↔ a.vertex = b.vertex :=
  ((G.embedRows ι).rotation_sameCycle_iff _ _).symm.trans
    ((FiniteReturn.sameCycle_congr _ _ (G.rowEmbeddingPorts ι) (G.rowEmbeddingPorts_rotation ι) a b).symm.trans
      (G.rotation_sameCycle_iff a b))

theorem rowEmbeddingPorts_boundary_iff (a : G.Dart) :
    (G.embedRows ι).IsBoundary (G.rowEmbeddingPorts ι a) ↔ G.IsBoundary a := by cases a <;> rfl

theorem rowEmbeddingPorts_boundaryDart (i : BoundaryIndex u v) :
    G.rowEmbeddingPorts ι (G.boundaryDart i) =
      (G.embedRows ι).boundaryDart (mapBoundaryIndex ι.edge u v i) := by cases i <;> rfl

theorem embedRows_boundaryNext (i : BoundaryIndex u v) :
    (G.embedRows ι).boundaryNext (mapBoundaryIndex ι.edge u v i) =
      mapBoundaryIndex ι.edge u v (G.boundaryNext i) := by
  have hr := MarkedReturn.perm_preserved_of_commutes (G.embedRows ι).circuitStep
    (G.embedRows ι).IsBoundary G.circuitStep G.IsBoundary (G.rowEmbeddingPorts ι)
    (G.rowEmbeddingPorts_circuitStep ι) (G.rowEmbeddingPorts_boundary_iff ι) (G.boundaryPorts i)
  have he : (⟨G.rowEmbeddingPorts ι (G.boundaryPorts i).val,
      (G.rowEmbeddingPorts_boundary_iff ι _).mpr (G.boundaryPorts i).property⟩ :
      Subtype (G.embedRows ι).IsBoundary) =
        (G.embedRows ι).boundaryPorts (mapBoundaryIndex ι.edge u v i) := by cases i <;> rfl
  rw [he, G.boundaryPorts_next, (G.embedRows ι).boundaryPorts_next] at hr
  apply (G.embedRows ι).boundaryDart.injective
  exact hr.symm.trans (G.rowEmbeddingPorts_boundaryDart ι _)

theorem embedRows_boundaryNoncrossing (h : G.BoundaryNoncrossing) :
    (G.embedRows ι).BoundaryNoncrossing :=
  h.transport (mapBoundaryIndex ι.edge u v) (mapBoundaryIndex_cyclic ι.edge u v)
    (G.embedRows_boundaryNext ι) (mapBoundaryIndex_between ι.edge u v)

theorem embedRows_boundarySeesComponents (h : G.BoundarySeesComponents) :
    (G.embedRows ι).BoundarySeesComponents := by
  intro x y
  obtain ⟨a, ha⟩ := (G.embedRows ι).boundaryPorts.surjective x
  obtain ⟨a, rfl⟩ := (mapBoundaryIndex ι.edge u v).surjective a
  obtain ⟨b, hb⟩ := (G.embedRows ι).boundaryPorts.surjective y
  obtain ⟨b, rfl⟩ := (mapBoundaryIndex ι.edge u v).surjective b
  rw [← ha, ← hb]
  have hc := connected_congr G.pairing.perm G.circuitStep (G.embedRows ι).pairing.perm
    (G.embedRows ι).circuitStep (G.rowEmbeddingPorts ι) (G.rowEmbeddingPorts_twin ι)
    (G.rowEmbeddingPorts_circuitStep ι) (G.boundaryDart a) (G.boundaryDart b)
  have hf := FiniteReturn.sameCycle_congr _ _ (G.rowEmbeddingPorts ι)
    (G.rowEmbeddingPorts_circuitStep ι) (G.boundaryDart a) (G.boundaryDart b)
  rw [G.rowEmbeddingPorts_boundaryDart, G.rowEmbeddingPorts_boundaryDart] at hc hf
  exact hc.symm.trans ((h (G.boundaryPorts a) (G.boundaryPorts b)).trans hf)

theorem embedRows_eulerDefect :
    eulerDefect (G.embedRows ι).pairing.perm (G.embedRows ι).circuitStep =
      eulerDefect G.pairing.perm G.circuitStep :=
  (eulerDefect_congr _ _ _ _ (G.rowEmbeddingPorts ι) (G.rowEmbeddingPorts_twin ι)
    (G.rowEmbeddingPorts_circuitStep ι)).symm

theorem embedRows_hub_relations :
    (∑ h : (G.embedRows ι).Hub, ([(G.embedRows ι).hubLabel h] : Multiset T)) =
      (∑ h : G.Hub, ([G.hubLabel h] : Multiset R)).map ι.vertex := by
  let F : Multiset R →+ Multiset T := {
    toFun := Multiset.map ι.vertex
    map_zero' := rfl
    map_add' := Multiset.map_add ι.vertex }
  exact (map_sum F (fun h : G.Hub => ([G.hubLabel h] : Multiset R)) Finset.univ).symm

end ThomGame.Pictures.PortGraph
