module

public import ThomGame.Construction.Numbering
public import ThomGame.Finite.WheelCentralRetract
public import ThomGame.Finite.HypergraphReindex
public import ThomGame.Finite.HypergraphMultiplicity
public import ThomGame.Finite.WheelCentralStellar

/-!
# Central-wheel retractions for the actual numbered matrix

The general incidence retraction is instantiated on every actual wheel
and transported along the proved row and column numbering bijections.
The target is the exact c/d neighbourhood of that wheel's third rows.
No five-sided-wheel retraction or picture normalization is assumed.
-/

@[expose] public section
namespace ThomGame.Construction

def centralWheelRetraction (r : WheelIndex) :
    Hypergraph.Retraction system.hypergraph (wheelFamily.centralNeighbourhood r) :=
  wheelFamily.centralRetraction r

def numberedCentralWheelRetraction (r : WheelIndex) :
    Hypergraph.Retraction numberedSystem.hypergraph (wheelFamily.centralNeighbourhood r) := by
  change Hypergraph.Retraction (system.reindex rowEquiv colEquiv).hypergraph _
  exact ((centralWheelRetraction r).reindexSource rowEquiv colEquiv).congrSource
    (SparseSystem.hypergraph_reindex system rowEquiv colEquiv).symm

theorem centralWheel_incidence (r : WheelIndex) (j : Fin (wheelFamily.size r)) :
    numberedSystem.hypergraph.incidence (rowEquiv ⟨r, j, 2⟩) =
      ([colEquiv (wheelFamily.aux r j 2), colEquiv (wheelFamily.aux r j 3),
        colEquiv (wheelFamily.aux r (finRotate (wheelFamily.size r) j) 3)] :
          Multiset (Fin 1889684)) := by
  simp [SparseSystem.hypergraph, numberedSystem, SparseSystem.reindex_column, system,
    Wheel.Family.system, Wheel.Family.columns]

theorem centralWheel_rhs_zero (r : WheelIndex) (j : Fin (wheelFamily.size r)) :
    numberedSystem.rhs (rowEquiv ⟨r, j, 2⟩) = 0 := by
  rw [numbered_rhs]
  exact wheelFamily.central_vertex_rhs_zero r j

theorem centralWheel_rim_incident (r : WheelIndex) (j : Fin (wheelFamily.size r))
    (row : Fin 1417152) :
    colEquiv (wheelFamily.aux r j 3) ∈ numberedSystem.hypergraph.incidence row ↔
      row = rowEquiv ⟨r, j, 2⟩ ∨ row = rowEquiv ⟨r, (finRotate (wheelFamily.size r)).symm j, 2⟩ := by
  obtain ⟨s, rfl⟩ := rowEquiv.surjective row
  simpa [numberedSystem, system, SparseSystem.hypergraph_reindex, Hypergraph.reindex_incidence,
    Multiset.mem_map, colEquiv.injective.eq_iff, rowEquiv.injective.eq_iff] using
      wheelFamily.central_rim_incident r j s

def centralWheelCycle (r : WheelIndex) : Hypergraph.Cycle system.hypergraph :=
  wheelFamily.centralCycle r (Nat.le_trans (by decide : 3 ≤ 4) (wheelWord_length_ge_four r))

def centralWheelStellar (r : WheelIndex) : (centralWheelCycle r).Stellar system.rhs :=
  wheelFamily.centralStellar r (Nat.le_trans (by decide : 3 ≤ 4) (wheelWord_length_ge_four r))

def numberedCentralWheelCycle (r : WheelIndex) : Hypergraph.Cycle numberedSystem.hypergraph where
  length := wheelFamily.size r
  length_ge_three := Nat.le_trans (by decide : 3 ≤ 4) (wheelWord_length_ge_four r)
  vertex := (wheelFamily.centralVertexInclusion r).trans rowEquiv.toEmbedding
  edge := (wheelFamily.centralRimInclusion r).trans colEquiv.toEmbedding
  edge_multiplicity row j := by
    change numberedSystem.hypergraph.multiplicity row (colEquiv (wheelFamily.aux r j 3)) = _
    rw [SparseSystem.hypergraph_multiplicity_eq_ite]
    exact ite_cond_congr (propext (centralWheel_rim_incident r j row))

def numberedCentralWheelStellar (r : WheelIndex) :
    (numberedCentralWheelCycle r).Stellar numberedSystem.rhs where
  retraction := numberedCentralWheelRetraction r
  vertex_eq _ := rfl
  rim_eq _ := rfl
  rhs_zero j := by
    have hv : (numberedCentralWheelCycle r).vertex j = rowEquiv ⟨r, j, 2⟩ := rfl
    rw [hv]
    exact centralWheel_rhs_zero r j

end ThomGame.Construction
