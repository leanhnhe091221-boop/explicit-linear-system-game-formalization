module

public import ThomGame.Analysis.MatrixProjectionRankOnePartition

/-!
# Refining an identity block into a partition with scalar gap everywhere

The same unitary tuple reduces the actual refinement. The old good
blocks keep their gap; the nonzero spectral pieces of the identity
block are rank one and satisfy every scalar-gap constant.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d h n : Nat}

structure MatrixScalarGapPartition (U : Fin h → UnitaryMatrix d) (c : ℝ) where
  n : Nat
  E : Fin n → CMatrix d
  projection : ∀ i, IsStarProjection (E i)
  orthogonal : Pairwise (fun i j => E i * E j = 0)
  sum_one : ∑ i, E i = 1
  reducing : ∀ i j, Commute (E i) (U j).val
  scalar_gap : ∀ i, E i ≠ 0 → ∀ X : CMatrix d, E i * X = X → X * E i = X →
    c * hsNorm (X - (normalizedTrace X / normalizedTrace (E i)) • E i) ^ 2 ≤
      matrixCoordinateEnergy U X

theorem matrixProjection_sub_identity {P q A : CMatrix d} (hP : IsStarProjection P)
    (hq : IsStarProjection q) (hle : q ≤ P) (hleft : P * A = P) (hright : A * P = P) :
    q * A = q ∧ A * q = q := by
  have hqP := (hq.le_iff_mul_eq_left hP).mp hle
  have hPq := (hq.le_iff_mul_eq_right hP).mp hle
  constructor
  · calc
      q * A = (q * P) * A := by rw [hqP]
      _ = q := by rw [Matrix.mul_assoc, hleft, hqP]
  · calc
      A * q = A * (P * q) := by rw [hPq]
      _ = q := by rw [← Matrix.mul_assoc, hright, hPq]

theorem exists_matrixScalarGapPartition_refinement [NeZero d]
    (U : Fin h → UnitaryMatrix d) (c : ℝ) (P : Option (Fin n) → CMatrix d)
    (hP : ∀ i, IsStarProjection (P i)) (horth : Pairwise (fun i j => P i * P j = 0))
    (hsum : ∑ i, P i = 1) (hred : ∀ i j, Commute (P i) (U j).val)
    (hbad : ∀ j, P none * (U j).val = P none)
    (hgap : ∀ i, P (some i) ≠ 0 → ∀ X : CMatrix d,
      P (some i) * X = X → X * P (some i) = X →
        c * hsNorm (X - (normalizedTrace X / normalizedTrace (P (some i))) • P (some i)) ^ 2 ≤
          matrixCoordinateEnergy U X) :
    ∃ Q : MatrixScalarGapPartition U c, Q.n = n + d := by
  let B := matrixProjectionRankOnePiece (hP none)
  let F : Fin (n + d) → CMatrix d := Fin.append (fun i => P (some i)) B
  have hB i : IsStarProjection (B i) := matrixProjectionRankOnePiece_isStarProjection (hP none) i
  have hBle i : B i ≤ P none := matrixProjectionRankOnePiece_le (hP none) i
  have hF (i : Fin (n + d)) : IsStarProjection (F i) := by
    refine Fin.addCases ?_ ?_ i
    · intro a
      simpa only [F, Fin.append_left] using hP (some a)
    · intro b
      simpa only [F, Fin.append_right] using hB b
  have hForth : Pairwise (fun i j => F i * F j = 0) := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro a j
      refine Fin.addCases ?_ ?_ j
      · intro b hab
        simp only [F, Fin.append_left]
        apply horth
        intro he
        cases he
        exact hab rfl
      · intro b _
        simp only [F, Fin.append_left, Fin.append_right]
        exact matrixProjection_subprojections_orthogonal (hP (some a)) (hB b)
          (hP (some a)) (hP none) le_rfl (hBle b) (horth (by simp))
    · intro a j
      refine Fin.addCases ?_ ?_ j
      · intro b _
        simp only [F, Fin.append_left, Fin.append_right]
        exact matrixProjection_subprojections_orthogonal (hB a) (hP (some b))
          (hP none) (hP (some b)) (hBle a) le_rfl (horth (by simp))
      · intro b hab
        simp only [F, Fin.append_right]
        apply matrixProjectionRankOnePiece_orthogonal (hP none)
        intro he
        subst b
        exact hab rfl
  have hFsum : ∑ i, F i = 1 := by
    rw [Fin.sum_univ_add]
    simp only [F, Fin.append_left, Fin.append_right]
    rw [show (∑ i, B i) = P none from matrixProjectionRankOnePiece_sum (hP none)]
    have he := hsum
    rw [Fintype.sum_option] at he
    simpa only [add_comm (P none)] using he
  have hBred (i : Fin d) (j : Fin h) : Commute (B i) (U j).val := by
    have he := matrixProjection_sub_identity (hP none) (hB i) (hBle i) (hbad j)
      ((hred none j).eq.symm.trans (hbad j))
    show B i * (U j).val = (U j).val * B i
    rw [he.1, he.2]
  have hFred (i : Fin (n + d)) (j : Fin h) : Commute (F i) (U j).val := by
    refine Fin.addCases ?_ ?_ i
    · intro a
      simpa only [F, Fin.append_left] using hred (some a) j
    · intro b
      simpa only [F, Fin.append_right] using hBred b j
  have hFgap (i : Fin (n + d)) : F i ≠ 0 → ∀ X : CMatrix d, F i * X = X → X * F i = X →
      c * hsNorm (X - (normalizedTrace X / normalizedTrace (F i)) • F i) ^ 2 ≤
        matrixCoordinateEnergy U X := by
    refine Fin.addCases ?_ ?_ i
    · intro a
      simpa only [F, Fin.append_left] using hgap a
    · intro b
      simp only [F, Fin.append_right]
      intro hb X hleft hright
      exact matrixRankOneCorner_scalar_gap U c (hB b)
        (matrixProjectionRankOnePiece_rank_eq (hP none) b hb) X hleft hright
  exact ⟨{
    n := n + d, E := F, projection := hF, orthogonal := hForth,
    sum_one := hFsum, reducing := hFred, scalar_gap := hFgap }, rfl⟩

theorem exists_matrixScalarGapPartition_identity [NeZero d] (h : Nat) (c : ℝ) :
    ∃ Q : MatrixScalarGapPartition (fun _ : Fin h => (1 : UnitaryMatrix d)) c, Q.n = d := by
  let hP := IsStarProjection.one (R := CMatrix d)
  refine ⟨{
    n := d, E := matrixProjectionRankOnePiece hP,
    projection := matrixProjectionRankOnePiece_isStarProjection hP,
    orthogonal := matrixProjectionRankOnePiece_orthogonal hP,
    sum_one := matrixProjectionRankOnePiece_sum hP,
    reducing := ?_, scalar_gap := ?_ }, rfl⟩
  · intro i j
    exact Commute.one_right _
  · intro i hi X hleft hright
    exact matrixRankOneCorner_scalar_gap _ c (matrixProjectionRankOnePiece_isStarProjection hP i)
      (matrixProjectionRankOnePiece_rank_eq hP i hi) X hleft hright

end ThomGame.Analysis
