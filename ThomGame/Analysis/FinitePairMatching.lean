module

public import Mathlib.Order.Preorder.Finite
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Basic.Real.Basic

/-!
# Finite matchings and the weight of their endpoints

A matching is an actual finite family of ordered pairs with distinct,
mutually disjoint endpoints. A maximal such family covers every edge.
The orientation only chooses one witness per matched pair.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators

variable {μ : Type*} [DecidableEq μ]

def finitePairEndpoints (e : μ × μ) : Finset μ := {e.1, e.2}

def finiteMatchingVertices (M : Finset (μ × μ)) : Finset μ := M.biUnion finitePairEndpoints

def IsFinitePairMatching (R : μ → μ → Prop) (M : Finset (μ × μ)) : Prop :=
  (∀ e ∈ M, R e.1 e.2 ∧ e.1 ≠ e.2) ∧
    (M : Set (μ × μ)).Pairwise (fun e f => Disjoint (finitePairEndpoints e) (finitePairEndpoints f))

@[simp] theorem mem_finitePairEndpoints (e : μ × μ) (v : μ) :
    v ∈ finitePairEndpoints e ↔ v = e.1 ∨ v = e.2 := by simp [finitePairEndpoints]

@[simp] theorem mem_finiteMatchingVertices (M : Finset (μ × μ)) (v : μ) :
    v ∈ finiteMatchingVertices M ↔ ∃ e ∈ M, v = e.1 ∨ v = e.2 := by
  simp [finiteMatchingVertices]

theorem exists_finitePairMatching_cover [Fintype μ] (R : μ → μ → Prop) :
    ∃ M : Finset (μ × μ), IsFinitePairMatching R M ∧
      ∀ i j, R i j → i ≠ j → i ∈ finiteMatchingVertices M ∨ j ∈ finiteMatchingVertices M := by
  classical
  let S : Set (Finset (μ × μ)) := {M | IsFinitePairMatching R M}
  have hnon : S.Nonempty := ⟨∅, by simp [S, IsFinitePairMatching]⟩
  obtain ⟨M, hM⟩ := (Set.toFinite S).exists_maximal hnon
  refine ⟨M, hM.1, ?_⟩
  intro i j hij hne
  by_contra h
  have hi : i ∉ finiteMatchingVertices M := fun hi => h (Or.inl hi)
  have hj : j ∉ finiteMatchingVertices M := fun hj => h (Or.inr hj)
  have hd (e : μ × μ) (he : e ∈ M) : Disjoint (finitePairEndpoints (i, j)) (finitePairEndpoints e) := by
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    rcases (mem_finitePairEndpoints _ _).mp hv with rfl | rfl
    · exact hi ((Finset.mem_biUnion).mpr ⟨e, he, hv'⟩)
    · exact hj ((Finset.mem_biUnion).mpr ⟨e, he, hv'⟩)
  have hnew : IsFinitePairMatching R (insert (i, j) M) := by
    constructor
    · intro e he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact ⟨hij, hne⟩
      · exact hM.1.1 e he
    · intro e he f hf hef
      rcases Finset.mem_insert.mp he with rfl | he
      · rcases Finset.mem_insert.mp hf with rfl | hf
        · exact (hef rfl).elim
        · exact hd f hf
      · rcases Finset.mem_insert.mp hf with rfl | hf
        · exact (hd e he).symm
        · exact hM.1.2 he hf hef
  have hsub : insert (i, j) M ⊆ M := hM.2 hnew (Finset.subset_insert _ _)
  have hm : (i, j) ∈ M := hsub (Finset.mem_insert_self _ _)
  exact hi ((mem_finiteMatchingVertices M i).mpr ⟨(i, j), hm, Or.inl rfl⟩)

theorem finitePairMatching_endpoint_weight {R : μ → μ → Prop} {M : Finset (μ × μ)}
    (hM : IsFinitePairMatching R M) (w : μ → ℝ) :
    ∑ i ∈ finiteMatchingVertices M, w i = ∑ e ∈ M, (w e.1 + w e.2) := by
  rw [finiteMatchingVertices, Finset.sum_biUnion hM.2]
  apply Finset.sum_congr rfl
  intro e he
  simp [finitePairEndpoints, (hM.1 e he).2]

theorem finitePairMatching_fst_injective {R : μ → μ → Prop} {M : Finset (μ × μ)}
    (hM : IsFinitePairMatching R M) : Function.Injective (fun e : M => e.val.1) := by
  intro e f he
  by_contra hne
  have hd := hM.2 e.property f.property (fun h => hne (Subtype.ext h))
  exact (Finset.disjoint_left.mp hd) (a := e.val.1) (by simp) (by simp [he])

theorem finitePairMatching_snd_injective {R : μ → μ → Prop} {M : Finset (μ × μ)}
    (hM : IsFinitePairMatching R M) : Function.Injective (fun e : M => e.val.2) := by
  intro e f he
  by_contra hne
  have hd := hM.2 e.property f.property (fun h => hne (Subtype.ext h))
  exact (Finset.disjoint_left.mp hd) (a := e.val.2) (by simp) (by simp [he])

end ThomGame.Analysis
