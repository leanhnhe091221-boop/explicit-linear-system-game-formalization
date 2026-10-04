module

public import ThomGame.Analysis.MatrixProjectionDeletionEnergy
public import ThomGame.Analysis.MatrixProjectionRankBounds

/-!
# The crossing obstruction in ALT Lemma 4.2

Almost expansion on a reducing projection prevents a low-energy
deleted part from first crossing one quarter of its trace. This
preserves the two invariants needed for finite-rank pruning.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d h : Nat} [NeZero d]

theorem matrixProjection_pruning_no_crossing (U : Fin h → UnitaryMatrix d)
    {P R : CMatrix d} (hP : IsStarProjection P) (hPne : P ≠ 0)
    (hR : IsStarProjection R) (hRP : R ≤ P) (hred : ∀ j, Commute P (U j).val)
    {κ ξ : ℝ} (hκ : 0 < κ) (hξ : ξ ≤ κ * matrixTraceReal d P / 16)
    (hexpand : ∀ a : CMatrix d, IsStarProjection a → a ≤ P → 2 * a.rank ≤ P.rank →
      κ * matrixTraceReal d a - ξ ≤ matrixCoordinateEnergy U a)
    (hsize : matrixTraceReal d (P - R) ≤ 3 * matrixTraceReal d P / 4)
    (henergy : matrixCoordinateEnergy U R ≤ κ / 16 * matrixTraceReal d (P - R)) :
    matrixTraceReal d (P - R) < matrixTraceReal d P / 4 := by
  have hTP := matrixTraceReal_projection_pos (NeZero.pos d) hP hPne
  have hF : IsStarProjection (P - R) := (hR.le_iff_sub hP).mp hRP
  have hFP : P - R ≤ P := sub_le_self _ hR.nonneg
  have htrace := matrixTraceReal_sub d P R
  by_contra hn
  have hcross : matrixTraceReal d P / 4 ≤ matrixTraceReal d (P - R) := not_lt.mp hn
  have hlower : κ * matrixTraceReal d P / 4 - ξ ≤ matrixCoordinateEnergy U R := by
    by_cases hhalf : matrixTraceReal d (P - R) ≤ matrixTraceReal d P / 2
    · have hh := hexpand (P - R) hF hFP
        ((matrixProjection_trace_le_half_iff (NeZero.pos d) hF hP).mp hhalf)
      rw [matrixCoordinateEnergy_reducing_sub U hred] at hh
      have hm := mul_le_mul_of_nonneg_left hcross hκ.le
      linarith only [hh, hm]
    · have hhalfR : matrixTraceReal d R ≤ matrixTraceReal d P / 2 := by
        linarith only [htrace, not_le.mp hhalf]
      have hquarterR : matrixTraceReal d P / 4 ≤ matrixTraceReal d R := by
        linarith only [htrace, hsize]
      have hh := hexpand R hR hRP
        ((matrixProjection_trace_le_half_iff (NeZero.pos d) hR hP).mp hhalfR)
      have hm := mul_le_mul_of_nonneg_left hquarterR hκ.le
      linarith only [hh, hm]
  have hm := mul_le_mul_of_nonneg_left hsize (div_nonneg hκ.le (by norm_num : (0 : ℝ) ≤ 16))
  have hp := mul_pos hκ hTP
  nlinarith only [hlower, henergy, hξ, hm, hp]

theorem matrixProjection_pruning_delete (U : Fin h → UnitaryMatrix d)
    {P Q p : CMatrix d} (hP : IsStarProjection P) (hPne : P ≠ 0)
    (hQ : IsStarProjection Q) (hQP : Q ≤ P) (hp : IsStarProjection p) (hpQ : p ≤ Q)
    (hred : ∀ j, Commute P (U j).val)
    {κ ξ : ℝ} (hκ : 0 < κ) (hξ : ξ ≤ κ * matrixTraceReal d P / 16)
    (hexpand : ∀ a : CMatrix d, IsStarProjection a → a ≤ P → 2 * a.rank ≤ P.rank →
      κ * matrixTraceReal d a - ξ ≤ matrixCoordinateEnergy U a)
    (hsize : matrixTraceReal d (P - Q) < matrixTraceReal d P / 4)
    (henergy : matrixCoordinateEnergy U Q ≤ κ / 16 * matrixTraceReal d (P - Q))
    (hhalf : matrixTraceReal d p ≤ matrixTraceReal d Q / 2)
    (hbad : matrixCompressedCoordinateEnergy U Q p < κ / 16 * matrixTraceReal d p) :
    matrixTraceReal d (P - (Q - p)) < matrixTraceReal d P / 4 ∧
      matrixCoordinateEnergy U (Q - p) ≤ κ / 16 * matrixTraceReal d (P - (Q - p)) := by
  have hR : IsStarProjection (Q - p) := (hp.le_iff_sub hQ).mp hpQ
  have hRP : Q - p ≤ P := (sub_le_self Q hp.nonneg).trans hQP
  have htrace : matrixTraceReal d (P - (Q - p)) =
      matrixTraceReal d (P - Q) + matrixTraceReal d p := by
    simp only [matrixTraceReal_sub]
    ring
  have hnew : matrixCoordinateEnergy U (Q - p) ≤ κ / 16 * matrixTraceReal d (P - (Q - p)) := by
    have hh := matrixCoordinateEnergy_projection_deletion_le U hp hQ hpQ
    rw [htrace]
    nlinarith only [hh, henergy, hbad]
  refine ⟨?_, hnew⟩
  apply matrixProjection_pruning_no_crossing U hP hPne hR hRP hred hκ hξ hexpand ?_ hnew
  have hTP := matrixTraceReal_nonneg d hP.nonneg
  have hTQ := matrixTraceReal_sub d P Q
  rw [htrace]
  linarith only [hsize, hhalf, hTQ, hTP]

end ThomGame.Analysis
