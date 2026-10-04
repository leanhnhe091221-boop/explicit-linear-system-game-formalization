module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Card
public import Mathlib.Basic.Real.Basic

/-!
# A median of an actual finite real family

Repeated values and empty index types are allowed. The strict lower
and strict upper sets each contain at most half of the indices.
-/

@[expose] public section
namespace ThomGame.Analysis

variable {ι : Type*} [Fintype ι]

theorem exists_finite_median (a : ι → ℝ) :
    ∃ m : ℝ, 2 * (Finset.univ.filter (fun i => a i < m)).card ≤ Fintype.card ι ∧
      2 * (Finset.univ.filter (fun i => m < a i)).card ≤ Fintype.card ι := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
    let := h
    exact ⟨0, by simp, by simp⟩
  | inr h =>
    let := h
    let L (t : ℝ) := Finset.univ.filter (fun i => a i < t)
    let A := Finset.univ.filter (fun i => 2 * (L (a i)).card ≤ Fintype.card ι)
    have hA : A.Nonempty := by
      obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ a Finset.univ_nonempty
      have hL : L (a i) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro j hj
        exact (not_lt_of_ge (hi j (Finset.mem_univ j))) (Finset.mem_filter.mp hj).2
      refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      rw [hL, Finset.card_empty, mul_zero]
      exact Nat.zero_le _
    obtain ⟨i, hiA, himax⟩ := Finset.exists_max_image A a hA
    refine ⟨a i, (Finset.mem_filter.mp hiA).2, ?_⟩
    let B := Finset.univ.filter (fun j => a i < a j)
    change 2 * B.card ≤ Fintype.card ι
    by_contra hn
    have hB : B.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨j, hjB, hjmin⟩ := Finset.exists_min_image B a hB
    have hsub : L (a j) ⊆ Bᶜ := by
      intro k hk
      apply Finset.mem_compl.mpr
      intro hkB
      exact (not_lt_of_ge (hjmin k hkB)) (Finset.mem_filter.mp hk).2
    have hcard := Finset.card_le_card hsub
    have hsum := Finset.card_compl_add_card B
    have hjA : j ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    exact (not_lt_of_ge (himax j hjA)) (Finset.mem_filter.mp hjB).2

end ThomGame.Analysis
