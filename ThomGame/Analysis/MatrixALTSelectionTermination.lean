module

public import ThomGame.Analysis.MatrixALTSelectionStep
public import ThomGame.Analysis.FinitePotentialTermination

/-!
# Termination of the actual ALT selection process

Uniform projection improvement yields actual minimum-rank selection
steps. The potential constructs a path of at most 8d steps ending at a
state with no eligible small-boundary projection.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d h : Nat} [NeZero d]

theorem exists_matrixALTSelection_terminal_path (U : Fin h → UnitaryMatrix d)
    {κ α : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) {R : CMatrix d} (hR : IsStarProjection R)
    (hcorrect : ∀ p, IsStarProjection p → p ≤ R →
      matrixCoordinateEnergy U p ≤ κ * (normalizedTrace p).re / 64 →
        ∃ F, MatrixProjectionImprovement U κ α p F) :
    ∃ n ≤ 8 * d, ∃ S : Nat → CMatrix d,
      S 0 = 1 - R ∧ (∀ i, 1 - R ≤ S i) ∧
      (¬∃ p, MatrixALTSelectionCandidate U κ R (S n) p) ∧
      ∀ i < n, MatrixALTSelectionStep U κ α R (S i) (S (i + 1)) := by
  let X := {S : CMatrix d // 1 - R ≤ S}
  let φ : X → ℝ := fun S => matrixALTSelectionPotential S.val
  let terminal : X → Prop := fun S => ¬∃ p, MatrixALTSelectionCandidate U κ R S.val p
  let step : X → X → Prop := fun S T => MatrixALTSelectionStep U κ α R S.val T.val
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hδ : 0 < 1 / (8 * (d : ℝ)) := by positivity
  have hupper : ∀ S : X, φ S ≤ 1 := fun S =>
    matrixALTSelectionPotential_le_one (hR.one_sub.nonneg.trans S.property)
  have hnext : ∀ S : X, ¬terminal S → ∃ T : X,
      step S T ∧ φ S + 1 / (8 * (d : ℝ)) ≤ φ T := by
    intro S hnot
    have hex : ∃ p, MatrixALTSelectionCandidate U κ R S.val p := Classical.not_not.mp hnot
    obtain ⟨T, hT⟩ := exists_matrixALTSelection_step U κ α hR hcorrect hex
    have hTbase : 1 - R ≤ T := S.property.trans (matrixALTSelectionStep_mono U hT)
    exact ⟨⟨T, hTbase⟩, hT, matrixALTSelectionStep_progress U hκ hκ1 hR S.property hT⟩
  let start : X := ⟨1 - R, le_rfl⟩
  have hbudget : 1 - ((8 * d : Nat) : ℝ) * (1 / (8 * (d : ℝ))) ≤ φ start := by
    have he : 1 - ((8 * d : Nat) : ℝ) * (1 / (8 * (d : ℝ))) = 0 := by
      push_cast
      field_simp
      norm_num
    rw [he]
    exact matrixALTSelectionPotential_nonneg hR.one_sub.nonneg
  obtain ⟨n, hn, path, hstart, hterm, hpath⟩ :=
    exists_finite_terminal_path φ terminal step hδ hupper hnext (8 * d) start hbudget
  exact ⟨n, hn, fun i => (path i).val, congrArg Subtype.val hstart,
    fun i => (path i).property, hterm, hpath⟩

end ThomGame.Analysis
