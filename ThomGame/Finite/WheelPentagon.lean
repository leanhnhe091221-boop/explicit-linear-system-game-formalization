module

public import ThomGame.Finite.WheelAuxIncidence
public import ThomGame.Finite.WheelCentralStellar

/-!
# The five-sided wheel cycles and their exact sun neighbourhoods

The rim is a_j, b_j, c_j, d_j, c_(j-1). Its five vertices and five
external spokes are given by the actual wheel rows and columns. This
module proves the closed cycle and neighbourhood conditions; it does
not assert the additional retraction of Slofstra Lemma 12.3.
-/

@[expose] public section
namespace ThomGame.Wheel.Family

variable {R V : Type*} [DecidableEq R] [DecidableEq V] (F : Family R V)

def pentagonVertex (r : R) (j : Fin (F.size r)) : Fin 5 → F.Row :=
  ![⟨r, j, 0⟩, ⟨r, j, 1⟩, ⟨r, j, 2⟩,
    ⟨r, (finRotate (F.size r)).symm j, 2⟩, ⟨r, (finRotate (F.size r)).symm j, 1⟩]

def pentagonRim (r : R) (j : Fin (F.size r)) : Fin 5 → F.Col :=
  ![F.aux r j 0, F.aux r j 1, F.aux r j 2, F.aux r j 3,
    F.aux r ((finRotate (F.size r)).symm j) 2]

def pentagonSpoke (r : R) (j : Fin (F.size r)) : Fin 5 → F.Col :=
  ![.inl (F.letter r j), F.aux r (finRotate (F.size r) j) 0,
    F.aux r (finRotate (F.size r) j) 3,
    F.aux r ((finRotate (F.size r)).symm j) 3, F.aux r ((finRotate (F.size r)).symm j) 1]

omit [DecidableEq R] [DecidableEq V] in
theorem prev_ne_self (r : R) (j : Fin (F.size r)) :
    (finRotate (F.size r)).symm j ≠ j := by
  intro h
  apply F.next_ne_self r j
  simpa using (congrArg (finRotate (F.size r)) h).symm

omit [DecidableEq R] [DecidableEq V] in
theorem pentagonVertex_injective (r : R) (j : Fin (F.size r)) :
    Function.Injective (F.pentagonVertex r j) := by
  have hp : j - 1 ≠ j := by simpa using F.prev_ne_self r j
  intro i k h
  fin_cases i <;> fin_cases k <;> simp [pentagonVertex, hp, Ne.symm hp] at h <;> rfl

omit [DecidableEq R] [DecidableEq V] in
theorem pentagonRim_injective (r : R) (j : Fin (F.size r)) :
    Function.Injective (F.pentagonRim r j) := by
  have hp : j - 1 ≠ j := by simpa using F.prev_ne_self r j
  intro i k h
  fin_cases i <;> fin_cases k <;> simp [pentagonRim, aux, hp, Ne.symm hp] at h <;> rfl

omit [DecidableEq R] [DecidableEq V] in
theorem pentagon_rim_incident (r : R) (j : Fin (F.size r)) (i : Fin 5) (row : F.Row) :
    F.pentagonRim r j i ∈ F.system.hypergraph.incidence row ↔
      row = F.pentagonVertex r j i ∨ row = F.pentagonVertex r j ((finRotate 5).symm i) := by
  fin_cases i <;>
    simp [pentagonRim, pentagonVertex, F.aux_incident, auxEndpoints, or_comm]

def pentagonCycle (r : R) (j : Fin (F.size r)) : Hypergraph.Cycle F.system.hypergraph where
  length := 5
  length_ge_three := by decide
  vertex := ⟨F.pentagonVertex r j, F.pentagonVertex_injective r j⟩
  edge := ⟨F.pentagonRim r j, F.pentagonRim_injective r j⟩
  edge_multiplicity row i := by
    rw [SparseSystem.hypergraph_multiplicity_eq_ite]
    exact ite_cond_congr (propext (F.pentagon_rim_incident r j i row))

theorem pentagon_edges_injective (r : R) (j : Fin (F.size r)) (hlen : 3 ≤ F.size r) :
    Function.Injective (Sum.elim (F.pentagonSpoke r j) (F.pentagonRim r j)) := by
  have hp : j - 1 ≠ j := by simpa using F.prev_ne_self r j
  have hn : j + 1 ≠ j := by simpa using F.next_ne_self r j
  have hnp : j + 1 ≠ j - 1 := by
    intro h
    have he : finRotate (F.size r) j = (finRotate (F.size r)).symm j := by simpa using h
    have hh := (F.centralCycle r hlen).next_next_ne_self j
    change finRotate (F.size r) (finRotate (F.size r) j) ≠ j at hh
    apply hh
    simpa only [Equiv.apply_symm_apply] using congrArg (finRotate (F.size r)) he
  rintro (i | i) (k | k) h <;> fin_cases i <;> fin_cases k <;>
    simp [pentagonSpoke, pentagonRim, aux, hp, Ne.symm hp, hn, Ne.symm hn,
      hnp, Ne.symm hnp] at h <;> rfl

def pentagonOpenEmbedding (r : R) (j : Fin (F.size r)) (hlen : 3 ≤ F.size r) :
    Hypergraph.OpenEmbedding (Hypergraph.sun 5) F.system.hypergraph where
  vertex := ⟨F.pentagonVertex r j, F.pentagonVertex_injective r j⟩
  edge := ⟨Sum.elim (F.pentagonSpoke r j) (F.pentagonRim r j), F.pentagon_edges_injective r j hlen⟩
  incidence i := by
    fin_cases i <;>
      simp [Hypergraph.sun, pentagonSpoke, pentagonRim, pentagonVertex,
        SparseSystem.hypergraph, system, columns]
    all_goals
      apply List.perm_iff_count.mpr
      intro e
      simp [List.count_cons, add_comm, add_left_comm]

def pentagonSunNeighbourhood (r : R) (j : Fin (F.size r)) (hlen : 3 ≤ F.size r) :
    (F.pentagonCycle r j).SunNeighbourhood where
  inclusion := F.pentagonOpenEmbedding r j hlen
  vertex_eq _ := rfl
  rim_eq _ := rfl

end ThomGame.Wheel.Family
