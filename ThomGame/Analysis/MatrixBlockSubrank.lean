module

public import ThomGame.Analysis.MatrixProjectionRankSums
public import ThomGame.Analysis.FiniteRankAllocation

/-!
# Prescribed rank inside an actual block diagonal projection

Rank is allocated across the orthogonal blocks. Each block receives
an actual spectral-basis subprojection, so the final sum still
commutes with every block of the original partition.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι μ : Type*} [Fintype ι] [Fintype μ] [DecidableEq ι]

omit [Fintype μ] in
theorem matrixProjection_blocks (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : ∀ i j, i ≠ j → E i * E j = 0)
    {Q : Matrix ι ι ℂ} (hQ : IsStarProjection Q) (hcomm : ∀ i, Commute (E i) Q) :
    (∀ i, IsStarProjection (E i * Q) ∧ E i * Q ≤ E i) ∧
      Pairwise (fun i j => (E i * Q) * (E j * Q) = 0) := by
  have hF (i : μ) := (hE i).mul hQ (hcomm i)
  refine ⟨fun i => ⟨hF i, (hF i |>.le_iff_mul_eq_left (hE i)).mpr ?_⟩, ?_⟩
  · calc
      E i * Q * E i = E i * (E i * Q) := by rw [Matrix.mul_assoc, ← (hcomm i).eq]
      _ = E i * Q := by rw [← Matrix.mul_assoc, (hE i).isIdempotentElem.eq]
  · intro i j hij
    calc
      (E i * Q) * (E j * Q) = E i * (Q * E j) * Q := by simp only [Matrix.mul_assoc]
      _ = E i * (E j * Q) * Q := by rw [← (hcomm j).eq]
      _ = 0 := by rw [← Matrix.mul_assoc (E i), horth i j hij, Matrix.zero_mul, Matrix.zero_mul]

theorem exists_matrixBlockSubprojection_rank (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : ∀ i j, i ≠ j → E i * E j = 0)
    (hsum : ∑ i, E i = 1) {Q : Matrix ι ι ℂ} (hQ : IsStarProjection Q)
    (hcomm : ∀ i, Commute (E i) Q) (n : Nat) (hn : n ≤ Q.rank) :
    ∃ R : Matrix ι ι ℂ, IsStarProjection R ∧ R ≤ Q ∧ R.rank = n ∧
      ∀ i, Commute (E i) R := by
  classical
  let F (i : μ) := E i * Q
  have hblocks := matrixProjection_blocks E hE horth hQ hcomm
  have hF (i : μ) : IsStarProjection (F i) := (hblocks.1 i).1
  have hFE (i : μ) : F i ≤ E i := (hblocks.1 i).2
  have horthF : Pairwise (fun i j => F i * F j = 0) := hblocks.2
  have hsumF : ∑ i, F i = Q := by simp only [F, ← Matrix.sum_mul, hsum, Matrix.one_mul]
  have hrankF : ∑ i, (F i).rank = Q.rank := by rw [← matrixProjection_sum_rank F hF horthF, hsumF]
  obtain ⟨k, hk, hksum⟩ := finite_rank_allocation (fun i => (F i).rank) n (hrankF.symm ▸ hn)
  choose R hR using fun i => exists_matrixSubprojection_rank (hF i) (k i) (hk i)
  have hRE (i : μ) : R i ≤ E i := (hR i).2.1.trans (hFE i)
  have horthR : Pairwise (fun i j => R i * R j = 0) := fun i j hij =>
    matrixProjection_subprojections_orthogonal (hR i).1 (hR j).1 (hE i) (hE j)
      (hRE i) (hRE j) (horth i j hij)
  refine ⟨∑ i, R i, matrixProjection_sum R (fun i => (hR i).1) horthR, ?_, ?_, ?_⟩
  · rw [← hsumF]
    exact Finset.sum_le_sum (fun i _ => (hR i).2.1)
  · rw [matrixProjection_sum_rank R (fun i => (hR i).1) horthR]
    simpa only [fun i => (hR i).2.2] using hksum
  · intro j
    show E j * (∑ i, R i) = (∑ i, R i) * E j
    rw [Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hij : i = j
    · subst i
      exact ((hR j).1.commute_of_le (hE j) (hRE j)).symm.eq
    · have hleft := matrixProjection_subprojections_orthogonal (hE j) (hR i).1
        (hE j) (hE i) le_rfl (hRE i) (horth j i (Ne.symm hij))
      have hright := matrixProjection_subprojections_orthogonal (hR i).1 (hE j)
        (hE i) (hE j) (hRE i) le_rfl (horth i j hij)
      exact hleft.trans hright.symm

theorem exists_matrixBlockProjection_rank (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : ∀ i j, i ≠ j → E i * E j = 0)
    (hsum : ∑ i, E i = 1) {Q : Matrix ι ι ℂ} (hQ : IsStarProjection Q)
    (hcomm : ∀ i, Commute (E i) Q) (n : Nat) (hn : n ≤ Fintype.card ι) :
    ∃ R : Matrix ι ι ℂ, IsStarProjection R ∧ R.rank = n ∧
      (R ≤ Q ∨ Q ≤ R) ∧ ∀ i, Commute (E i) R := by
  by_cases hsmall : n ≤ Q.rank
  · obtain ⟨R, hR, hle, hrank, hc⟩ := exists_matrixBlockSubprojection_rank E hE horth hsum hQ hcomm n hsmall
    exact ⟨R, hR, hrank, Or.inl hle, hc⟩
  · have hcomp : ∀ i, Commute (E i) (1 - Q) := fun i => (Commute.one_right _).sub_right (hcomm i)
    have hr := matrixProjection_rank_one_sub_add hQ
    have hn' : Fintype.card ι - n ≤ (1 - Q).rank := by omega
    obtain ⟨S, hS, hle, hs, hc⟩ := exists_matrixBlockSubprojection_rank E hE horth hsum hQ.one_sub hcomp _ hn'
    refine ⟨1 - S, hS.one_sub, ?_, Or.inr ?_, fun i => (Commute.one_right _).sub_right (hc i)⟩
    · have he := matrixProjection_rank_one_sub_add hS
      omega
    · simpa only [le_sub_iff_add_le, add_comm] using hle

end ThomGame.Analysis
