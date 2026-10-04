module

public import ThomGame.Finite.Hypergraph
public import ThomGame.Finite.WheelSystem

/-!
# The central wheel neighbourhood is a retract

This is the actual map of Slofstra Lemma 12.2. The target vertices are
the third-family rows of one selected wheel; its edges are that wheel's
c and d variables. Ordinary edges and all other wheels are deleted.
On the selected wheel, a, b and d map to d, and c maps to c. First-family
rows disappear with two equal images; the other two families map to the
corresponding third-family row.
-/

@[expose] public section
namespace ThomGame.Wheel.Family

variable {R V : Type*} (F : Family R V)

abbrev CentralVertex (r : R) := Fin (F.size r)
abbrev CentralEdge (r : R) := Fin (F.size r) ⊕ Fin (F.size r)

def centralNeighbourhood (r : R) : Hypergraph (F.CentralVertex r) (F.CentralEdge r) where
  incidence j := [Sum.inl j, Sum.inr j, Sum.inr (finRotate (F.size r) j)]

def centralVertexInclusion (r : R) : F.CentralVertex r ↪ F.Row where
  toFun j := ⟨r, j, 2⟩
  inj' := by intro i j h; cases h; rfl

def centralEdgeInclusion (r : R) : F.CentralEdge r ↪ F.Col where
  toFun
    | .inl j => F.aux r j 2
    | .inr j => F.aux r j 3
  inj' := by
    rintro (i | i) (j | j) h <;> simp_all [aux]

def centralOpenEmbedding (r : R) :
    Hypergraph.OpenEmbedding (F.centralNeighbourhood r) F.system.hypergraph where
  vertex := F.centralVertexInclusion r
  edge := F.centralEdgeInclusion r
  incidence j := by
    simp [centralNeighbourhood, centralVertexInclusion, centralEdgeInclusion,
      SparseSystem.hypergraph, system, columns]

variable [DecidableEq R]

def centralRetractVertex (r : R) : F.Row → Option (F.CentralVertex r)
  | ⟨s, j, k⟩ => if h : s = r then
      if k = 0 then none else some (Fin.cast (congrArg F.size h) j)
    else none

def centralRetractEdge (r : R) : F.Col → Option (F.CentralEdge r)
  | .inl _ => none
  | .inr ⟨s, j, k⟩ => if h : s = r then
      some (if k = 2 then .inl (Fin.cast (congrArg F.size h) j) else .inr (Fin.cast (congrArg F.size h) j))
    else none

theorem centralRetractVertex_self (r : R) (j : Fin (F.size r)) (k : Fin 3) :
    F.centralRetractVertex r ⟨r, j, k⟩ = if k = 0 then none else some j := by
  simp [centralRetractVertex]

theorem centralRetractEdge_aux (r : R) (j : Fin (F.size r)) (k : Fin 4) :
    F.centralRetractEdge r (F.aux r j k) = some (if k = 2 then .inl j else .inr j) := by
  simp [centralRetractEdge, aux]

theorem centralRetained_other (r s : R) (hrs : s ≠ r) (j : Fin (F.size s)) (k : Fin 3) :
    (F.system.hypergraph.incidence ⟨s, j, k⟩).filterMap (F.centralRetractEdge r) = 0 := by
  fin_cases k <;>
    simp [SparseSystem.hypergraph, system, columns, centralRetractEdge, aux, hrs]

theorem centralRetained_first (r : R) (j : Fin (F.size r)) :
    (F.system.hypergraph.incidence ⟨r, j, 0⟩).filterMap (F.centralRetractEdge r) =
      (([Sum.inr j, Sum.inr j] : List (F.CentralEdge r)) : Multiset (F.CentralEdge r)) := by
  change Multiset.filterMap (F.centralRetractEdge r)
    (Sum.inl (F.letter r j) ::ₘ F.aux r j 0 ::ₘ F.aux r j 1 ::ₘ 0) = _
  rw [Multiset.filterMap_cons_none _ _ rfl,
    Multiset.filterMap_cons_some _ _ _ (by simpa using F.centralRetractEdge_aux r j 0),
    Multiset.filterMap_cons_some _ _ _ (by simpa using F.centralRetractEdge_aux r j 1)]
  rfl

theorem centralRetained_second (r : R) (j : Fin (F.size r)) :
    (F.system.hypergraph.incidence ⟨r, j, 1⟩).filterMap (F.centralRetractEdge r) =
      (F.centralNeighbourhood r).incidence j := by
  simp [SparseSystem.hypergraph, system, columns, centralRetractEdge, aux, centralNeighbourhood]
  exact List.Perm.swap _ _ _

theorem centralRetained_third (r : R) (j : Fin (F.size r)) :
    (F.system.hypergraph.incidence ⟨r, j, 2⟩).filterMap (F.centralRetractEdge r) =
      (F.centralNeighbourhood r).incidence j := by
  simp [SparseSystem.hypergraph, system, columns, centralRetractEdge, aux, centralNeighbourhood]

def centralGeneralizedHom (r : R) : Hypergraph.GeneralizedHom F.system.hypergraph (F.centralNeighbourhood r) where
  vertex := F.centralRetractVertex r
  edge := F.centralRetractEdge r
  retained := by
    rintro ⟨s, j, k⟩ w hw
    by_cases hsr : s = r
    · subst s
      fin_cases k
      · simp [centralRetractVertex] at hw
      · have hj : j = w := by simpa [centralRetractVertex] using hw
        subst w
        exact F.centralRetained_second r j
      · have hj : j = w := by simpa [centralRetractVertex] using hw
        subst w
        exact F.centralRetained_third r j
    · simp [centralRetractVertex, hsr] at hw
  deleted := by
    rintro ⟨s, j, k⟩ hv
    by_cases hsr : s = r
    · subst s
      fin_cases k
      · change Even ((F.system.hypergraph.incidence ⟨r, j, 0⟩).filterMap (F.centralRetractEdge r)).card ∧
          Hypergraph.Monochromatic ((F.system.hypergraph.incidence ⟨r, j, 0⟩).filterMap (F.centralRetractEdge r))
        rw [F.centralRetained_first r j]
        constructor
        · exact ⟨1, rfl⟩
        · intro e he f hf
          simp only [Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false, or_self] at he hf
          exact he.trans hf.symm
      · simp [centralRetractVertex] at hv
      · simp [centralRetractVertex] at hv
    · rw [F.centralRetained_other r s hsr j k]
      constructor
      · exact ⟨0, rfl⟩
      · intro e he
        exact (Multiset.notMem_zero e he).elim

/-- The open central neighbourhood is an actual generalized retract of
the complete wheel family, including all ordinary shared edges. -/
def centralRetraction (r : R) : Hypergraph.Retraction F.system.hypergraph (F.centralNeighbourhood r) where
  inclusion := F.centralOpenEmbedding r
  retract := F.centralGeneralizedHom r
  vertex_leftInverse j := by simp [centralGeneralizedHom, centralOpenEmbedding, centralVertexInclusion,
    centralRetractVertex]
  edge_leftInverse e := by
    cases e <;> simp [centralGeneralizedHom, centralOpenEmbedding, centralEdgeInclusion,
      centralRetractEdge, aux]

omit [DecidableEq R] in
theorem central_vertex_rhs_zero (r : R) (j : F.CentralVertex r) :
    F.system.rhs (F.centralVertexInclusion r j) = 0 := by
  simp [system, centralVertexInclusion]

omit [DecidableEq R] in
theorem central_rim_incident (r : R) (j : Fin (F.size r)) (row : F.Row) :
    F.aux r j 3 ∈ F.system.hypergraph.incidence row ↔
      row = ⟨r, j, 2⟩ ∨ row = ⟨r, (finRotate (F.size r)).symm j, 2⟩ := by
  classical
  rcases row with ⟨s, i, k⟩
  by_cases hsr : s = r
  · subst s
    have hn : j = finRotate (F.size r) i ↔ i = (finRotate (F.size r)).symm j := by
      rw [Equiv.eq_symm_apply]
      exact eq_comm
    fin_cases k
    · simp [SparseSystem.hypergraph, system, columns, aux]
    · simp [SparseSystem.hypergraph, system, columns, aux]
    · simpa [SparseSystem.hypergraph, system, columns, aux, eq_comm] using
        or_congr (eq_comm (a := j) (b := i)) hn
  · have hrs : r ≠ s := Ne.symm hsr
    fin_cases k <;> simp [SparseSystem.hypergraph, system, columns, aux, hsr, hrs]

end ThomGame.Wheel.Family
