module

public import ThomGame.Pictures.RowEdgeFibers

/-!
# Actual lifts of a closed hypergraph path

Covered path edges give successive equivalences of the actual hub
fibers. Composing these equivalences enumerates all occurrences of the
path vertices by a starting hub and a position, with the actual paired
darts witnessing every step.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open scoped Classical

variable {R S : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}

structure RowPath (A : SparseSystem R S) where
  length : Nat
  vertex : Fin (length + 1) ↪ R
  edge : Fin length ↪ S
  incident : ∀ v i, edge i ∈ A.hypergraph.incidence v ↔
    v = vertex i.castSucc ∨ v = vertex i.succ

namespace RowPath

def cycleVertexIndex (C : Hypergraph.Cycle A.hypergraph) (start n : Nat)
    (hn : start + n < C.length) : Fin (n + 1) ↪ Fin C.length where
  toFun i := ⟨start + i.val, by omega⟩
  inj' i j he := Fin.ext (by have hh := congrArg Fin.val he; dsimp at hh; omega)

def cycleEdgeIndex (C : Hypergraph.Cycle A.hypergraph) (start n : Nat)
    (hn : start + n < C.length) : Fin n ↪ Fin C.length where
  toFun i := ⟨start + i.val + 1, by omega⟩
  inj' i j he := Fin.ext (by have hh := congrArg Fin.val he; dsimp at hh; omega)

def ofCycleSegment (C : Hypergraph.Cycle A.hypergraph) (start n : Nat)
    (hn : start + n < C.length) : RowPath A where
  length := n
  vertex := (cycleVertexIndex C start n hn).trans C.vertex
  edge := (cycleEdgeIndex C start n hn).trans C.edge
  incident v i := by
    have hp : (finRotate C.length).symm (cycleEdgeIndex C start n hn i) =
        cycleVertexIndex C start n hn i.castSucc := by
      apply Fin.ext
      rw [coe_finRotate_symm_of_ne_zero]
      · change start + i.val + 1 - 1 = start + i.val
        omega
      · intro he
        have hh := congrArg Fin.val he
        change start + i.val + 1 = 0 at hh
        omega
    have he : cycleEdgeIndex C start n hn i = cycleVertexIndex C start n hn i.succ := Fin.ext rfl
    exact (C.incident_iff v (cycleEdgeIndex C start n hn i)).trans (by rw [hp, he]; exact or_comm)

variable (P : RowPath A) (G : SolutionGroup.RowGraph A [] []) [IsEmpty G.Joint]
  (hc : ∀ x : G.Dart, Port.label G.jointLabel x ∈ Set.range P.edge → G.EdgeHasDistinctHubLabels x)

noncomputable def edgeHubEquiv (i : Fin P.length) :
    G.LabelHub (P.vertex i.castSucc) ≃ G.LabelHub (P.vertex i.succ) :=
  rowEdgeHubEquiv _ _ (P.edge i)
    ((P.incident _ i).mpr (Or.inl rfl)) ((P.incident _ i).mpr (Or.inr rfl))
    (fun v hv => (P.incident v i).mp hv) (fun x hx => hc x ⟨i, hx.symm⟩)

noncomputable def lift : (i : Fin (P.length + 1)) → G.LabelHub (P.vertex 0) ≃ G.LabelHub (P.vertex i) :=
  Fin.induction (Equiv.refl _) (fun i e => e.trans (P.edgeHubEquiv G hc i))

omit [DecidableEq R] [DecidableEq S] in
theorem lift_zero (h : G.LabelHub (P.vertex 0)) : P.lift G hc 0 h = h := rfl

omit [DecidableEq R] [DecidableEq S] in
theorem lift_succ (i : Fin P.length) (h : G.LabelHub (P.vertex 0)) :
    P.lift G hc i.succ h = P.edgeHubEquiv G hc i (P.lift G hc i.castSucc h) := rfl

noncomputable def hub (h : G.LabelHub (P.vertex 0)) (i : Fin (P.length + 1)) : G.Hub :=
  (P.lift G hc i h).val

omit [DecidableEq R] [DecidableEq S] in
theorem hub_label (h : G.LabelHub (P.vertex 0)) (i : Fin (P.length + 1)) :
    G.hubLabel (P.hub G hc h i) = P.vertex i := (P.lift G hc i h).property

omit [DecidableEq R] [DecidableEq S] in
theorem hub_injective : Function.Injective (fun hi : G.LabelHub (P.vertex 0) × Fin (P.length + 1) =>
    P.hub G hc hi.1 hi.2) := by
  rintro ⟨h, i⟩ ⟨k, j⟩ he
  have hij : i = j := P.vertex.injective
    ((P.hub_label G hc h i).symm.trans ((congrArg G.hubLabel he).trans (P.hub_label G hc k j)))
  subst j
  have hhk : h = k := (P.lift G hc i).injective (Subtype.ext he)
  exact Prod.ext hhk rfl

noncomputable def hubEquiv : G.LabelHub (P.vertex 0) × Fin (P.length + 1) ≃
    {h : G.Hub // G.hubLabel h ∈ Set.range P.vertex} :=
  Equiv.ofBijective (fun hi => ⟨P.hub G hc hi.1 hi.2, ⟨hi.2, (P.hub_label G hc hi.1 hi.2).symm⟩⟩)
    ⟨fun _ _ he => P.hub_injective G hc (congrArg Subtype.val he), by
      rintro ⟨h, i, hi⟩
      refine ⟨((P.lift G hc i).symm ⟨h, hi.symm⟩, i), Subtype.ext ?_⟩
      change (P.lift G hc i ((P.lift G hc i).symm ⟨h, hi.symm⟩)).val = h
      exact congrArg (fun k : G.LabelHub (P.vertex i) => k.val)
        ((P.lift G hc i).apply_symm_apply ⟨h, hi.symm⟩)⟩

omit [DecidableEq R] [DecidableEq S] in
theorem lift_edge (h : G.LabelHub (P.vertex 0)) (i : Fin P.length) :
    ∃ x : G.Dart, x.vertex = .inr (.inl (P.hub G hc h i.castSucc)) ∧
      (G.pairing.twin x).vertex = .inr (.inl (P.hub G hc h i.succ)) ∧
      Port.label G.jointLabel x = P.edge i :=
  rowEdgeHubEquiv_edge _ _ (P.edge i)
    ((P.incident _ i).mpr (Or.inl rfl)) ((P.incident _ i).mpr (Or.inr rfl))
    (fun v hv => (P.incident v i).mp hv) (fun x hx => hc x ⟨i, hx.symm⟩) (P.lift G hc i.castSucc h)

omit [DecidableEq R] [DecidableEq S] in
theorem lift_edge_unique (h : G.LabelHub (P.vertex 0)) (i : Fin P.length) :
    ∃! x : G.Dart, x.vertex = .inr (.inl (P.hub G hc h i.castSucc)) ∧
      (G.pairing.twin x).vertex = .inr (.inl (P.hub G hc h i.succ)) ∧
      Port.label G.jointLabel x = P.edge i := by
  obtain ⟨x, hx, hy, he⟩ := P.lift_edge G hc h i
  exact ⟨x, ⟨hx, hy, he⟩, fun y hy =>
    G.row_label_injective_at_vertex (hy.1.trans hx.symm) (hy.2.2.trans he.symm)⟩

omit [DecidableEq R] [DecidableEq S] in
theorem seed_eq_of_edge (h k : G.LabelHub (P.vertex 0)) (i : Fin P.length) (x : G.Dart)
    (hx : x.vertex = .inr (.inl (P.hub G hc h i.castSucc)))
    (hy : (G.pairing.twin x).vertex = .inr (.inl (P.hub G hc k i.succ)))
    (he : Port.label G.jointLabel x = P.edge i) : h = k := by
  have hh := rowEdgeHubEquiv_eq_of_edge _ _ (P.edge i)
    ((P.incident _ i).mpr (Or.inl rfl)) ((P.incident _ i).mpr (Or.inr rfl))
    (fun v hv => (P.incident v i).mp hv) (fun x hx => hc x ⟨i, hx.symm⟩)
    (P.lift G hc i.castSucc h) (P.lift G hc i.succ k) x hx hy he
  exact (P.lift G hc i.succ).injective hh

end RowPath
end ThomGame.Pictures.PortGraph
