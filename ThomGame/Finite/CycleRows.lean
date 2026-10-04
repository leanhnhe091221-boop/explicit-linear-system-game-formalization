module

public import ThomGame.Finite.HypergraphCycles

/-! # Exactly two row slots belong to a closed hypergraph cycle -/

@[expose] public section
namespace ThomGame.Hypergraph.Cycle

variable {R S : Type*} [DecidableEq R] [DecidableEq S]
  {A : SparseSystem R S} (C : Cycle A.hypergraph)

theorem row_rim_indices (j : Fin C.length) :
    ∃ i₀ i₁ : Fin 3, i₀ ≠ i₁ ∧
      ∀ i, A.column (C.vertex j) i ∈ Set.range C.edge ↔ i = i₀ ∨ i = i₁ := by
  obtain ⟨i₀, hi₀⟩ := (A.mem_hypergraph_incidence _ _).mp
    ((C.incident_index_iff j j).mpr (Or.inl rfl))
  obtain ⟨i₁, hi₁⟩ := (A.mem_hypergraph_incidence _ _).mp
    ((C.incident_index_iff j (finRotate C.length j)).mpr (Or.inr rfl))
  refine ⟨i₀, i₁, ?_, fun i => ?_⟩
  · intro he
    have hh := hi₀.symm.trans ((congrArg (A.column (C.vertex j)) he).trans hi₁)
    exact C.next_ne_self j (C.edge.injective hh).symm
  · constructor
    · rintro ⟨k, hk⟩
      have hki : C.edge k ∈ A.hypergraph.incidence (C.vertex j) := by
        rw [hk]
        exact (A.mem_hypergraph_incidence _ _).mpr ⟨i, rfl⟩
      rcases (C.incident_index_iff j k).mp hki with rfl | rfl
      · exact Or.inl (A.column_injective _ (hk.symm.trans hi₀.symm))
      · exact Or.inr (A.column_injective _ (hk.symm.trans hi₁.symm))
    · rintro (rfl | rfl)
      · exact ⟨j, hi₀.symm⟩
      · exact ⟨finRotate C.length j, hi₁.symm⟩

theorem row_rim_card (j : Fin C.length) :
    Fintype.card {i : Fin 3 // A.column (C.vertex j) i ∈ Set.range C.edge} = 2 := by
  classical
  obtain ⟨i₀, i₁, hne, hiff⟩ := C.row_rim_indices j
  rw [Fintype.card_subtype]
  have he : Finset.univ.filter (fun i => A.column (C.vertex j) i ∈ Set.range C.edge) = {i₀, i₁} := by
    ext i
    simp [hiff]
  rw [he, Finset.card_pair hne]

end ThomGame.Hypergraph.Cycle
