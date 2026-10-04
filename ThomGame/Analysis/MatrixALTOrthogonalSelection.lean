module

public import ThomGame.Analysis.MatrixALTTerminalCorrection

/-!
# Actual selected and orthogonally corrected ALT data

This record retains the minimum-rank choices and every intermediate
state, so the later expansion argument applies to the same selected
projections. Both weighted estimates use these original states.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d h : Nat}

theorem matrixFiniteTrajectory_partialSum {n : Nat} (S : Nat → CMatrix d) (F : Fin n → CMatrix d)
    {S₀ : CMatrix d} (hzero : S 0 = S₀) (hstep : ∀ i : Fin n, S (i.val + 1) = S i + F i)
    (k : Nat) (hk : k ≤ n) : S k = matrixProjectionPartialSum S₀ (matrixExtendFiniteFamily F) k := by
  induction k with
  | zero => simpa only [matrixProjectionPartialSum_zero] using hzero
  | succ k ih =>
    have hkn : k < n := by omega
    rw [hstep ⟨k, hkn⟩, matrixProjectionPartialSum_succ, ih (by omega),
      matrixExtendFiniteFamily_apply F ⟨k, hkn⟩]

theorem matrixProjectionImprovement_rank_lt_twice [NeZero d] (U : Fin h → UnitaryMatrix d)
    {κ α : ℝ} {p F : CMatrix d} (hp : IsStarProjection p) (hne : p ≠ 0)
    (hI : MatrixProjectionImprovement U κ α p F) : F.rank < 2 * p.rank := by
  have he := hI.2.2.2.1
  simp only [normalizedTrace_re] at he
  change matrixTraceReal d F ≤ (5 / 3 : ℝ) * matrixTraceReal d p at he
  rw [matrixTraceReal_projection_rank d hI.1, matrixTraceReal_projection_rank d hp,
    ← mul_div_assoc] at he
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hr := (div_le_div_iff_of_pos_right hd).mp he
  have hp0 : (0 : ℝ) < p.rank := Nat.cast_pos.mpr (matrixProjection_rank_pos hp hne)
  have hh : (F.rank : ℝ) < 2 * (p.rank : ℝ) := by linarith only [hr, hp0]
  exact_mod_cast hh

structure MatrixALTOrthogonalSelection (U : Fin h → UnitaryMatrix d) (κ α η : ℝ) (R : CMatrix d) where
  n : Nat
  length_le : n ≤ 8 * d
  S : Nat → CMatrix d
  P : Fin n → CMatrix d
  F : Fin n → CMatrix d
  V : Fin n → CMatrix d
  state_zero : S 0 = 1 - R
  state_ge : ∀ i, 1 - R ≤ S i
  selection : ∀ i : Fin n, MatrixALTSelectionCandidate U κ R (S i) (P i) ∧
    (∀ q, MatrixALTSelectionCandidate U κ R (S i) q → (P i).rank ≤ q.rank) ∧
    MatrixProjectionImprovement U κ α (P i) (F i) ∧ S (i.val + 1) = S i + F i
  terminal : ¬∃ p, MatrixALTSelectionCandidate U κ R (S n) p
  state_total : S n = (1 - R) + ∑ i, F i
  selected_trace : (∑ i, matrixTraceReal d (P i)) ≤ 8
  corrected_trace : (∑ i, matrixTraceReal d (F i)) ≤ 8 / 3
  corrected_energy : (∑ i, matrixCoordinateEnergy U (F i)) ≤ 8 * α
  initial_projection : ∀ i, IsStarProjection ((V i)ᴴ * V i)
  final_projection : ∀ i, IsStarProjection (V i * (V i)ᴴ)
  initial_orthogonal : Pairwise (fun i j => ((V i)ᴴ * V i) * ((V j)ᴴ * V j) = 0)
  rank_le : ∀ i, ((V i)ᴴ * V i).rank ≤ (F i).rank
  rank_gap : ∀ i, (F i).rank < 2 * (P i).rank
  energy : (∑ i, matrixCoordinateEnergy U (V i)) ≤ 1184 * η ^ 2
  initial_energy : (∑ i, matrixCoordinateEnergy U ((V i)ᴴ * V i)) ≤ 4736 * η ^ 2
  weighted_trace : (∑ i : Fin n, matrixTraceReal d ((S i) ^ 2 * (V i * (V i)ᴴ))) ≤ 3 * η
  leakage : (∑ i : Fin n, matrixTraceReal d
    ((1 - matrixClosedLowSpectralCut (S i) (κ / 512)) * (V i * (V i)ᴴ))) ≤ 3 * (512 / κ) ^ 2 * η
  bad_projection : IsStarProjection (1 - ∑ i, (V i)ᴴ * V i)
  bad_trace : matrixTraceReal d (1 - ∑ i, (V i)ᴴ * V i) ≤ 16 * η

theorem exists_matrixALTOrthogonalSelection [NeZero d] [NeZero h] (U : Fin h → UnitaryMatrix d)
    {R : CMatrix d} (hR : IsStarProjection R) {κ α η : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hα : 0 ≤ α) (hη : 0 < η) (hη8 : η ≤ 1 / 8)
    (hηκ : η ≤ κ / 1024) (hsmall : (1 + 61440 / (κ * Real.sqrt κ)) * η ≤ 1)
    (hαη : α ≤ η ^ 4) (hexp : 9 * α ≤ Real.exp (-(η ^ 4)⁻¹))
    (hRtrace : matrixTraceReal d (1 - R) ≤ α)
    (hcorrect : ∀ p, IsStarProjection p → p ≤ R →
      matrixCoordinateEnergy U p ≤ κ * (normalizedTrace p).re / 64 →
        ∃ F, MatrixProjectionImprovement U κ α p F) :
    Nonempty (MatrixALTOrthogonalSelection U κ α η R) := by
  obtain ⟨n, hn, S, P, F, hzero, hge, hsel, hterm, htotal, hPt, hFt, hFe⟩ :=
    exists_matrixALTSelection_family U hκ hκ1 hα hR hcorrect
  have hF (i : Fin n) : IsStarProjection (F i) := (hsel i).2.2.1.1
  have hstop : ¬∃ p, MatrixALTSelectionCandidate U κ R ((1 - R) + ∑ i, F i) p := by
    rwa [htotal] at hterm
  obtain ⟨V, hVi, hVf, horth, hrank, hVe, hPe, hweight, hleak, hbad, hbadtrace⟩ :=
    exists_matrixALT_terminal_orthogonalCorrection U hR F hF hκ hκ1 hη hη8 hηκ hsmall
      hαη hexp hRtrace hFt hFe hstop
  have hprefix (i : Fin n) : S i = matrixProjectionPartialSum (1 - R) (matrixExtendFiniteFamily F) i :=
    matrixFiniteTrajectory_partialSum S F hzero (fun i => (hsel i).2.2.2) i i.isLt.le
  refine ⟨{
    n := n, length_le := hn, S := S, P := P, F := F, V := V
    state_zero := hzero, state_ge := hge, selection := hsel, terminal := hterm, state_total := htotal
    selected_trace := hPt, corrected_trace := hFt, corrected_energy := hFe
    initial_projection := hVi, final_projection := hVf, initial_orthogonal := horth
    rank_le := hrank, rank_gap := ?_, energy := hVe, initial_energy := hPe
    weighted_trace := ?_, leakage := ?_, bad_projection := hbad, bad_trace := hbadtrace }⟩
  · intro i
    exact matrixProjectionImprovement_rank_lt_twice U (hsel i).1.1 (hsel i).1.2.1 (hsel i).2.2.1
  · simpa only [hprefix] using hweight
  · simpa only [hprefix] using hleak

end ThomGame.Analysis
