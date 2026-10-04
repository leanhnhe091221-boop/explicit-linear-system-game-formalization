module

public import ThomGame.Analysis.MatrixProjectionPruningStep

/-!
# Actual retained projections in ALT Lemma 4.2

Minimize the natural-number rank among actual projections satisfying
the trace and energy invariants. Any bad nonzero subprojection could
be deleted while preserving the invariants, contradicting minimality.
No termination or projection-existence certificate is assumed.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d h : Nat} [NeZero d]

theorem exists_matrixPrunedProjection (U : Fin h → UnitaryMatrix d)
    {P : CMatrix d} (hP : IsStarProjection P) (hPne : P ≠ 0)
    (hred : ∀ j, Commute P (U j).val)
    {κ ξ : ℝ} (hκ : 0 < κ) (hξ : ξ ≤ κ * matrixTraceReal d P / 16)
    (hexpand : ∀ a : CMatrix d, IsStarProjection a → a ≤ P → 2 * a.rank ≤ P.rank →
      κ * matrixTraceReal d a - ξ ≤ matrixCoordinateEnergy U a) :
    ∃ e : CMatrix d, IsStarProjection e ∧ e ≤ P ∧ e ≠ 0 ∧
      matrixTraceReal d (P - e) < matrixTraceReal d P / 4 ∧
      matrixCoordinateEnergy U e ≤ κ / 16 * matrixTraceReal d (P - e) ∧
      matrixTraceReal d (P - e) ≤ 2 * ξ / κ ∧
      matrixCoordinateEnergy U e ≤ ξ / 8 ∧
      ∀ p : CMatrix d, IsStarProjection p → p ≤ e → 2 * p.rank ≤ e.rank →
        κ / 16 * matrixTraceReal d p ≤ matrixCompressedCoordinateEnergy U e p := by
  classical
  let good : CMatrix d → Prop := fun Q => IsStarProjection Q ∧ Q ≤ P ∧
    matrixTraceReal d (P - Q) < matrixTraceReal d P / 4 ∧
    matrixCoordinateEnergy U Q ≤ κ / 16 * matrixTraceReal d (P - Q)
  have hTP := matrixTraceReal_projection_pos (NeZero.pos d) hP hPne
  have hgoodP : good P := by
    refine ⟨hP, le_rfl, ?_, ?_⟩
    · simpa only [sub_self, matrixTraceReal_zero] using div_pos hTP (by norm_num : (0 : ℝ) < 4)
    · rw [matrixCoordinateEnergy_eq_zero_of_reducing U hred, sub_self, matrixTraceReal_zero, mul_zero]
  have hex : ∃ n : Nat, ∃ Q : CMatrix d, good Q ∧ Q.rank = n := ⟨P.rank, P, hgoodP, rfl⟩
  obtain ⟨Q, hgoodQ, hrank⟩ := Nat.find_spec hex
  obtain ⟨hQ, hQP, hsize, henergy⟩ := hgoodQ
  have hQne : Q ≠ 0 := by
    intro hz
    rw [hz, sub_zero] at hsize
    linarith only [hsize, hTP]
  have hgap : ∀ p : CMatrix d, IsStarProjection p → p ≤ Q → 2 * p.rank ≤ Q.rank →
      κ / 16 * matrixTraceReal d p ≤ matrixCompressedCoordinateEnergy U Q p := by
    intro p hp hpQ hhalf
    by_cases hpzero : p = 0
    · subst p
      simpa only [matrixTraceReal_zero, mul_zero] using matrixCompressedCoordinateEnergy_nonneg U Q 0
    by_contra hn
    have hbad : matrixCompressedCoordinateEnergy U Q p < κ / 16 * matrixTraceReal d p := not_le.mp hn
    have hnew := matrixProjection_pruning_delete U hP hPne hQ hQP hp hpQ hred hκ hξ hexpand
      hsize henergy ((matrixProjection_trace_le_half_iff (NeZero.pos d) hp hQ).mpr hhalf) hbad
    have hgoodR : good (Q - p) :=
      ⟨(hp.le_iff_sub hQ).mp hpQ, (sub_le_self Q hp.nonneg).trans hQP, hnew⟩
    have hmin : Nat.find hex ≤ (Q - p).rank := Nat.find_min' hex ⟨Q - p, hgoodR, rfl⟩
    have hlt := matrixProjection_rank_sub_lt hQ hp hpQ hpzero
    omega
  have hF : IsStarProjection (P - Q) := (hQ.le_iff_sub hP).mp hQP
  have hFP : P - Q ≤ P := sub_le_self _ hQ.nonneg
  have hhalfF : matrixTraceReal d (P - Q) ≤ matrixTraceReal d P / 2 := by
    linarith only [hsize, hTP]
  have hbound := hexpand (P - Q) hF hFP
    ((matrixProjection_trace_le_half_iff (NeZero.pos d) hF hP).mp hhalfF)
  rw [matrixCoordinateEnergy_reducing_sub U hred] at hbound
  have hFpos := matrixTraceReal_nonneg d hF.nonneg
  have hκF := mul_nonneg hκ.le hFpos
  have hmass : matrixTraceReal d (P - Q) ≤ 2 * ξ / κ := by
    apply (le_div_iff₀ hκ).mpr
    nlinarith only [hbound, henergy, hκF]
  have hE : matrixCoordinateEnergy U Q ≤ ξ / 8 := by
    have hm := (le_div_iff₀ hκ).mp hmass
    nlinarith only [henergy, hm]
  exact ⟨Q, hQ, hQP, hQne, hsize, henergy, hmass, hE, hgap⟩

theorem exists_matrixPrunedOrDiscardedProjection (U : Fin h → UnitaryMatrix d)
    {P : CMatrix d} (hP : IsStarProjection P) (hred : ∀ j, Commute P (U j).val)
    {κ ξ : ℝ} (hκ : 0 < κ) (hξ : 0 ≤ ξ)
    (hexpand : ∀ a : CMatrix d, IsStarProjection a → a ≤ P → 2 * a.rank ≤ P.rank →
      κ * matrixTraceReal d a - ξ ≤ matrixCoordinateEnergy U a) :
    ∃ e : CMatrix d, IsStarProjection e ∧ e ≤ P ∧
      matrixCoordinateEnergy U e ≤ ξ / 8 ∧
      matrixTraceReal d (P - e) ≤ 16 * ξ / κ ∧
      ∀ p : CMatrix d, IsStarProjection p → p ≤ e → 2 * p.rank ≤ e.rank →
        κ / 16 * matrixTraceReal d p ≤ matrixCompressedCoordinateEnergy U e p := by
  have hzero : matrixCoordinateEnergy U 0 = 0 :=
    matrixCoordinateEnergy_eq_zero_of_reducing U (fun j => Commute.zero_left (U j).val)
  have hgapzero : ∀ p : CMatrix d, IsStarProjection p → p ≤ 0 → 2 * p.rank ≤ (0 : CMatrix d).rank →
      κ / 16 * matrixTraceReal d p ≤ matrixCompressedCoordinateEnergy U 0 p := by
    intro p hp hp0 _
    have he : p = 0 := le_antisymm hp0 hp.nonneg
    rw [he, matrixTraceReal_zero, mul_zero]
    exact matrixCompressedCoordinateEnergy_nonneg U 0 0
  by_cases hPzero : P = 0
  · refine ⟨0, IsStarProjection.zero _, hP.nonneg, ?_, ?_, hgapzero⟩
    · rw [hzero]
      positivity
    · rw [hPzero, sub_self, matrixTraceReal_zero]
      positivity
  by_cases hsmall : ξ ≤ κ * matrixTraceReal d P / 16
  · obtain ⟨e, he, hle, _, _, _, hmass, henergy, hgap⟩ :=
      exists_matrixPrunedProjection U hP hPzero hred hκ hsmall hexpand
    refine ⟨e, he, hle, henergy, hmass.trans ?_, hgap⟩
    apply div_le_div_of_nonneg_right _ hκ.le
    linarith only [hξ]
  · refine ⟨0, IsStarProjection.zero _, hP.nonneg, ?_, ?_, hgapzero⟩
    · rw [hzero]
      positivity
    · rw [sub_zero]
      apply (le_div_iff₀ hκ).mpr
      nlinarith only [not_le.mp hsmall]

end ThomGame.Analysis
