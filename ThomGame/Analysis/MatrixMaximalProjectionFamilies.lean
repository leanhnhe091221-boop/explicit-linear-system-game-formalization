module

public import ThomGame.Analysis.MatrixRandomSignSums
public import Mathlib.Order.SuccPred.Archimedean

/-!
# Maximal finite orthogonal families of matrix projections

Nonzero orthogonal projections are linearly independent in the actual
trace Hilbert space. Their cardinalities are bounded by its finite
dimension, so every predicate on nonzero projections has a maximal
finite orthogonal family, including the empty family when appropriate.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator

variable {d : Nat}

theorem matrixProjection_mul_zero_symm {P Q : CMatrix d} (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) (h : P * Q = 0) : Q * P = 0 := by
  simpa only [star_mul, hP.isSelfAdjoint.star_eq, hQ.isSelfAdjoint.star_eq, star_zero] using congrArg star h

variable [NeZero d]

theorem matrixOrthogonalFinset_card_le (s : Finset (CMatrix d))
    (hP : ∀ P ∈ s, IsStarProjection P) (hne : ∀ P ∈ s, P ≠ 0)
    (horth : (s : Set (CMatrix d)).Pairwise (fun P Q => P * Q = 0)) :
    s.card ≤ Module.finrank ℂ (FiniteMatrixHilbert d) := by
  have hlin : LinearIndependent ℂ (fun i : s => finiteMatrixHilbertEquiv d i.val) := by
    apply linearIndependent_of_ne_zero_of_inner_eq_zero
    · intro i hi
      apply hne i.val i.prop
      apply (finiteMatrixHilbertEquiv d).injective
      simpa only [map_zero] using hi
    · intro i j hij
      rw [finiteMatrixHilbert_inner, (hP i.val i.prop).isSelfAdjoint.star_eq,
        horth i.prop j.prop (fun he => hij (Subtype.ext he)), normalizedTrace_zero]
  simpa only [Fintype.card_coe] using hlin.fintype_card_le_finrank

theorem exists_matrixMaximalOrthogonalFamily (B : CMatrix d → Prop)
    (hB : ∀ P, B P → IsStarProjection P ∧ P ≠ 0) :
    ∃ s : Finset (CMatrix d), (∀ P ∈ s, B P) ∧ (s : Set (CMatrix d)).Pairwise (fun P Q => P * Q = 0) ∧
      ∀ Q, B Q → ¬(∀ P ∈ s, P * Q = 0) := by
  classical
  let good : Finset (CMatrix d) → Prop := fun s =>
    (∀ P ∈ s, B P) ∧ (s : Set (CMatrix d)).Pairwise (fun P Q => P * Q = 0)
  let cards : Set Nat := {n | ∃ s, good s ∧ s.card = n}
  have hb : BddAbove cards := by
    refine ⟨Module.finrank ℂ (FiniteMatrixHilbert d), ?_⟩
    rintro n ⟨s, hs, rfl⟩
    exact matrixOrthogonalFinset_card_le s (fun P hP => (hB P (hs.1 P hP)).1)
      (fun P hP => (hB P (hs.1 P hP)).2) hs.2
  have hn : cards.Nonempty := ⟨0, ∅, ⟨by simp, by simp⟩, rfl⟩
  obtain ⟨n, ⟨s, hs, hsn⟩, hmax⟩ := hb.exists_isGreatest_of_nonempty hn
  refine ⟨s, hs.1, hs.2, ?_⟩
  intro Q hQ hQorth
  have hQnot : Q ∉ s := by
    intro hQs
    have he := hQorth Q hQs
    rw [(hB Q hQ).1.isIdempotentElem.eq] at he
    exact (hB Q hQ).2 he
  have hi : good (insert Q s) := by
    constructor
    · intro P hP
      rcases Finset.mem_insert.mp hP with rfl | hP
      · exact hQ
      · exact hs.1 P hP
    · intro P hP R hR hPR
      rcases Finset.mem_insert.mp hP with hPQ | hP
      · rcases Finset.mem_insert.mp hR with hRQ | hR
        · exact False.elim (hPR (hPQ.trans hRQ.symm))
        · rw [hPQ]
          exact matrixProjection_mul_zero_symm (hB R (hs.1 R hR)).1 (hB Q hQ).1 (hQorth R hR)
      · rcases Finset.mem_insert.mp hR with hRQ | hR
        · rw [hRQ]
          exact hQorth P hP
        · exact hs.2 hP hR hPR
  have hcard := hmax (show (insert Q s).card ∈ cards from ⟨insert Q s, hi, rfl⟩)
  rw [Finset.card_insert_of_notMem hQnot, ← hsn] at hcard
  omega

end ThomGame.Analysis
