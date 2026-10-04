module

public import ThomGame.Construction.Numbering
public import ThomGame.Finite.WheelPentagon
public import ThomGame.Finite.HypergraphReindex

/-!
# The actual numbered five-sided wheel cycles

Both the rim's global incidence and its complete sun neighbourhood are
transported to the actual row and column numbers. No pentagon retraction
or constellation normalization theorem is assumed here.
-/

@[expose] public section
namespace ThomGame.Construction

def pentagonWheelCycle (r : WheelIndex) (j : Fin (wheelFamily.size r)) :
    Hypergraph.Cycle system.hypergraph := wheelFamily.pentagonCycle r j

def pentagonWheelSunNeighbourhood (r : WheelIndex) (j : Fin (wheelFamily.size r)) :
    (pentagonWheelCycle r j).SunNeighbourhood :=
  wheelFamily.pentagonSunNeighbourhood r j
    (Nat.le_trans (by decide : 3 ≤ 4) (wheelWord_length_ge_four r))

theorem numbered_pentagon_rim_incident (r : WheelIndex) (j : Fin (wheelFamily.size r))
    (i : Fin 5) (row : Fin 1417152) :
    colEquiv (wheelFamily.pentagonRim r j i) ∈ numberedSystem.hypergraph.incidence row ↔
      row = rowEquiv (wheelFamily.pentagonVertex r j i) ∨
        row = rowEquiv (wheelFamily.pentagonVertex r j ((finRotate 5).symm i)) := by
  obtain ⟨s, rfl⟩ := rowEquiv.surjective row
  simpa [numberedSystem, system, SparseSystem.hypergraph_reindex, Hypergraph.reindex_incidence,
    Multiset.mem_map, colEquiv.injective.eq_iff, rowEquiv.injective.eq_iff] using
      wheelFamily.pentagon_rim_incident r j i s

def numberedPentagonWheelCycle (r : WheelIndex) (j : Fin (wheelFamily.size r)) :
    Hypergraph.Cycle numberedSystem.hypergraph where
  length := 5
  length_ge_three := by decide
  vertex := (pentagonWheelCycle r j).vertex.trans rowEquiv.toEmbedding
  edge := (pentagonWheelCycle r j).edge.trans colEquiv.toEmbedding
  edge_multiplicity row i := by
    change numberedSystem.hypergraph.multiplicity row (colEquiv (wheelFamily.pentagonRim r j i)) = _
    rw [SparseSystem.hypergraph_multiplicity_eq_ite]
    exact ite_cond_congr (propext (numbered_pentagon_rim_incident r j i row))

def numberedPentagonWheelOpenEmbedding (r : WheelIndex) (j : Fin (wheelFamily.size r)) :
    Hypergraph.OpenEmbedding (Hypergraph.sun 5) numberedSystem.hypergraph :=
  (((pentagonWheelSunNeighbourhood r j).inclusion).reindexTarget rowEquiv colEquiv).congrTarget
    (SparseSystem.hypergraph_reindex system rowEquiv colEquiv).symm

def numberedPentagonWheelSunNeighbourhood (r : WheelIndex) (j : Fin (wheelFamily.size r)) :
    (numberedPentagonWheelCycle r j).SunNeighbourhood where
  inclusion := numberedPentagonWheelOpenEmbedding r j
  vertex_eq _ := rfl
  rim_eq _ := rfl

end ThomGame.Construction
