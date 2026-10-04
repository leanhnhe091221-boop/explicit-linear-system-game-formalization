module

public import ThomGame.Analysis.MatrixALTSelectionTermination

/-!
# The selected finite family and the totals in ALT (4.9)

The actual terminating path supplies minimum-rank projections and their
actual corrections. Telescoping the bounded potential gives total
selected trace at most 8, corrected trace at most 8/3, and corrected
boundary energy at most 8 alpha.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d h : Nat} [NeZero d]

theorem exists_matrixALTSelection_family (U : Fin h → UnitaryMatrix d)
    {κ α : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hα : 0 ≤ α) {R : CMatrix d} (hR : IsStarProjection R)
    (hcorrect : ∀ p, IsStarProjection p → p ≤ R →
      matrixCoordinateEnergy U p ≤ κ * (normalizedTrace p).re / 64 →
        ∃ F, MatrixProjectionImprovement U κ α p F) :
    ∃ n ≤ 8 * d, ∃ (S : Nat → CMatrix d) (P F : Fin n → CMatrix d),
      S 0 = 1 - R ∧ (∀ i, 1 - R ≤ S i) ∧
      (∀ i : Fin n, MatrixALTSelectionCandidate U κ R (S i) (P i) ∧
        (∀ q, MatrixALTSelectionCandidate U κ R (S i) q → (P i).rank ≤ q.rank) ∧
        MatrixProjectionImprovement U κ α (P i) (F i) ∧ S (i.val + 1) = S i + F i) ∧
      (¬∃ p, MatrixALTSelectionCandidate U κ R (S n) p) ∧
      S n = (1 - R) + ∑ i, F i ∧
      (∑ i, matrixTraceReal d (P i)) ≤ 8 ∧
      (∑ i, matrixTraceReal d (F i)) ≤ 8 / 3 ∧
      (∑ i, matrixCoordinateEnergy U (F i)) ≤ 8 * α := by
  classical
  obtain ⟨n, hn, S, hS0, hSbase, hterm, hpath⟩ :=
    exists_matrixALTSelection_terminal_path U hκ hκ1 hR hcorrect
  have hw (i : Fin n) : ∃ p F : CMatrix d,
      MatrixALTSelectionCandidate U κ R (S i) p ∧
      (∀ q, MatrixALTSelectionCandidate U κ R (S i) q → p.rank ≤ q.rank) ∧
      MatrixProjectionImprovement U κ α p F ∧ S (i.val + 1) = S i + F := hpath i i.isLt
  choose P F hP hmin hI hSstep using hw
  have hpos (i : Nat) : 0 ≤ S i := hR.one_sub.nonneg.trans (hSbase i)
  have hincrement (i : Fin n) : (3 / 8 : ℝ) * matrixTraceReal d (F i) ≤
      matrixALTSelectionPotential (S (i.val + 1)) - matrixALTSelectionPotential (S i) := by
    rw [hSstep i]
    exact matrixALTSelection_corrected_increment (hpos i) hR (hSbase i) hκ.le hκ1
      (hP i).1 (hI i).1 (hP i).2.2.1
      (matrixProjectionImprovement_ALT_distance U hκ (hP i).2.2.2.le (hI i))
  have hsuminc := Finset.sum_le_sum (s := Finset.univ) fun i _ => hincrement i
  rw [← Finset.mul_sum,
    Fin.sum_univ_eq_sum_range (fun k => matrixALTSelectionPotential (S (k + 1)) - matrixALTSelectionPotential (S k)),
    Finset.sum_range_sub (fun k => matrixALTSelectionPotential (S k))] at hsuminc
  have hsumF : (∑ i, matrixTraceReal d (F i)) ≤ 8 / 3 := by
    have hu := matrixALTSelectionPotential_le_one (hpos n)
    have hl := matrixALTSelectionPotential_nonneg (hpos 0)
    linarith only [hsuminc, hu, hl]
  have htrace (i : Fin n) : (1 / 3 : ℝ) * matrixTraceReal d (P i) ≤ matrixTraceReal d (F i) := by
    simpa only [normalizedTrace_re, matrixTraceReal] using (hI i).2.2.1
  have hsumtrace := Finset.sum_le_sum (s := Finset.univ) fun i _ => htrace i
  rw [← Finset.mul_sum] at hsumtrace
  have hsumP : (∑ i, matrixTraceReal d (P i)) ≤ 8 := by linarith only [hsumtrace, hsumF]
  have henergy (i : Fin n) : matrixCoordinateEnergy U (F i) ≤ α * matrixTraceReal d (P i) := by
    simpa only [normalizedTrace_re, matrixTraceReal] using (hI i).2.2.2.2
  have hsumE := Finset.sum_le_sum (s := Finset.univ) fun i _ => henergy i
  rw [← Finset.mul_sum] at hsumE
  have hsumE' : (∑ i, matrixCoordinateEnergy U (F i)) ≤ 8 * α :=
    hsumE.trans (by nlinarith only [mul_le_mul_of_nonneg_left hsumP hα])
  have hsumstate : (∑ i : Fin n, F i) = S n - S 0 := by
    calc
      _ = ∑ i : Fin n, (S (i.val + 1) - S i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hSstep i]
        abel
      _ = _ := by rw [Fin.sum_univ_eq_sum_range (fun k => S (k + 1) - S k), Finset.sum_range_sub S]
  refine ⟨n, hn, S, P, F, hS0, hSbase,
    fun i => ⟨hP i, hmin i, hI i, hSstep i⟩, hterm, ?_, hsumP, hsumF, hsumE'⟩
  rw [hsumstate, hS0]
  abel

end ThomGame.Analysis
