module

public import ThomGame.Finite.WheelCentralRetract
public import ThomGame.Finite.HypergraphCycles
public import ThomGame.Finite.HypergraphMultiplicity

/-! # The actual central rim is a stellar cycle -/

@[expose] public section
namespace ThomGame.Wheel.Family

variable {R V : Type*} [DecidableEq R] [DecidableEq V] (F : Family R V)

def centralRimInclusion (r : R) : Fin (F.size r) ↪ F.Col where
  toFun j := F.aux r j 3
  inj' := by intro i j h; simpa [aux] using h

def centralCycle (r : R) (hlen : 3 ≤ F.size r) : Hypergraph.Cycle F.system.hypergraph where
  length := F.size r
  length_ge_three := hlen
  vertex := F.centralVertexInclusion r
  edge := F.centralRimInclusion r
  edge_multiplicity row j := by
    change F.system.hypergraph.multiplicity row (F.aux r j 3) = _
    rw [SparseSystem.hypergraph_multiplicity_eq_ite]
    exact ite_cond_congr (propext (F.central_rim_incident r j row))

def centralStellar (r : R) (hlen : 3 ≤ F.size r) :
    (F.centralCycle r hlen).Stellar F.system.rhs where
  retraction := F.centralRetraction r
  vertex_eq _ := rfl
  rim_eq _ := rfl
  rhs_zero j := F.central_vertex_rhs_zero r j

end ThomGame.Wheel.Family
