module

public import ThomGame.Analysis.MatrixALTSelectionOverlap
public import ThomGame.Analysis.MatrixMarkovProjectionImprovement
public import ThomGame.Analysis.MatrixProjectionRankBounds

/-!
# Actual minimum-rank selection and correction in ALT Step 1

Candidates are nonzero low-boundary projections below the range of the
actual polar factor. A least rank exists whenever a candidate exists.
The proved projection-improvement conclusion supplies a corrected next
state, and every such step raises the potential by at least 1/(8d).
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d h : Nat}

def MatrixALTSelectionCandidate (U : Fin h → UnitaryMatrix d) (κ : ℝ) (R S p : CMatrix d) : Prop :=
  IsStarProjection p ∧ p ≠ 0 ∧
    p ≤ matrixRectPolar (R * matrixClosedLowSpectralCut S (κ / 512)) *
      (matrixRectPolar (R * matrixClosedLowSpectralCut S (κ / 512)))ᴴ ∧
    matrixCoordinateEnergy U p < κ / 64 * matrixTraceReal d p

def MatrixALTSelectionStep (U : Fin h → UnitaryMatrix d) (κ α : ℝ) (R S T : CMatrix d) : Prop :=
  ∃ p F : CMatrix d, MatrixALTSelectionCandidate U κ R S p ∧
    (∀ q, MatrixALTSelectionCandidate U κ R S q → p.rank ≤ q.rank) ∧
    MatrixProjectionImprovement U κ α p F ∧ T = S + F

theorem exists_matrixALTSelection_minimal (U : Fin h → UnitaryMatrix d) (κ : ℝ) (R S : CMatrix d)
    (hex : ∃ p, MatrixALTSelectionCandidate U κ R S p) :
    ∃ p, MatrixALTSelectionCandidate U κ R S p ∧
      ∀ q, MatrixALTSelectionCandidate U κ R S q → p.rank ≤ q.rank := by
  classical
  have hn : ∃ n : Nat, ∃ p, MatrixALTSelectionCandidate U κ R S p ∧ p.rank = n := by
    obtain ⟨p, hp⟩ := hex
    exact ⟨p.rank, p, hp, rfl⟩
  obtain ⟨p, hp, hrank⟩ := Nat.find_spec hn
  refine ⟨p, hp, ?_⟩
  intro q hq
  rw [hrank]
  exact Nat.find_min' hn ⟨q, hq, rfl⟩

theorem matrixProjectionImprovement_ALT_distance (U : Fin h → UnitaryMatrix d)
    {κ α : ℝ} (hκ : 0 < κ) {p F : CMatrix d}
    (henergy : matrixCoordinateEnergy U p ≤ κ / 64 * matrixTraceReal d p)
    (hI : MatrixProjectionImprovement U κ α p F) :
    hsNorm (F - p) ^ 2 ≤ (9 / 16 : ℝ) * matrixTraceReal d p := by
  have he := mul_le_mul_of_nonneg_left henergy (by positivity : 0 ≤ 36 * κ⁻¹)
  have halg : 36 * κ⁻¹ * (κ / 64 * matrixTraceReal d p) = (9 / 16 : ℝ) * matrixTraceReal d p := by
    field_simp
    ring
  rw [halg] at he
  exact hI.2.1.trans he

theorem exists_matrixALTSelection_step (U : Fin h → UnitaryMatrix d) (κ α : ℝ)
    {R S : CMatrix d} (hR : IsStarProjection R)
    (hcorrect : ∀ p, IsStarProjection p → p ≤ R →
      matrixCoordinateEnergy U p ≤ κ * (normalizedTrace p).re / 64 →
        ∃ F, MatrixProjectionImprovement U κ α p F)
    (hex : ∃ p, MatrixALTSelectionCandidate U κ R S p) :
    ∃ T, MatrixALTSelectionStep U κ α R S T := by
  obtain ⟨p, hp, hmin⟩ := exists_matrixALTSelection_minimal U κ R S hex
  have hpR : p ≤ R := hp.2.2.1.trans (matrixProjectionPolar_final_le hR)
  have he : matrixCoordinateEnergy U p ≤ κ * (normalizedTrace p).re / 64 := by
    have hh := hp.2.2.2.le
    simpa only [normalizedTrace_re, matrixTraceReal, div_mul_eq_mul_div] using hh
  obtain ⟨F, hF⟩ := hcorrect p hp.1 hpR he
  exact ⟨S + F, p, F, hp, hmin, hF, rfl⟩

theorem matrixALTSelectionStep_mono (U : Fin h → UnitaryMatrix d) {κ α : ℝ} {R S T : CMatrix d}
    (hstep : MatrixALTSelectionStep U κ α R S T) : S ≤ T := by
  obtain ⟨_, F, _, _, hF, rfl⟩ := hstep
  exact le_add_of_nonneg_right hF.1.nonneg

theorem matrixTraceReal_nonzero_projection_ge_inv [NeZero d] {p : CMatrix d}
    (hp : IsStarProjection p) (hne : p ≠ 0) : (d : ℝ)⁻¹ ≤ matrixTraceReal d p := by
  rw [matrixTraceReal_projection_rank d hp, ← one_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg d)
  exact_mod_cast matrixProjection_rank_pos hp hne

theorem matrixALTSelectionStep_progress [NeZero d] (U : Fin h → UnitaryMatrix d)
    {κ α : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) {R S T : CMatrix d}
    (hR : IsStarProjection R) (hSR : 1 - R ≤ S)
    (hstep : MatrixALTSelectionStep U κ α R S T) :
    matrixALTSelectionPotential S + 1 / (8 * (d : ℝ)) ≤ matrixALTSelectionPotential T := by
  obtain ⟨p, F, hp, _, hF, rfl⟩ := hstep
  have hS : 0 ≤ S := hR.one_sub.nonneg.trans hSR
  have hclose := matrixProjectionImprovement_ALT_distance U hκ hp.2.2.2.le hF
  have hi := matrixALTSelection_corrected_increment hS hR hSR hκ.le hκ1 hp.1 hF.1 hp.2.2.1 hclose
  have ht := hF.2.2.1
  have hpdim := matrixTraceReal_nonzero_projection_ge_inv hp.1 hp.2.1
  simp only [normalizedTrace_re] at ht
  change (1 / 3 : ℝ) * matrixTraceReal d p ≤ matrixTraceReal d F at ht
  have hdim : 1 / (8 * (d : ℝ)) = (1 / 8 : ℝ) * (d : ℝ)⁻¹ := by ring
  rw [hdim]
  linarith

end ThomGame.Analysis
