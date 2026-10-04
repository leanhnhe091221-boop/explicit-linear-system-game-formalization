module

public import ThomGame.Analysis.FiniteNoDriftExplicitCertificate
public import ThomGame.Construction.PaperExplicitGapReduction

/-! The explicit double obstruction follows from the three robust spectral gaps. -/

@[expose] public section
namespace ThomGame.Analysis

open Construction

theorem finiteNoDrift_paper_defect_small : paperExplicitDefect ≤ 1 / (10 : ℝ) ^ 40 := by
  have hn : 200 ≤ (2 : ℕ) ^ 50000 :=
    (by norm_num : 200 ≤ (2 : ℕ) ^ 8).trans
      (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by decide : 8 ≤ 50000))
  exact (finiteALT_half_pow_antitone hn).trans (by norm_num)

theorem finiteNoDrift_explicit_double_of_weakGaps {d : ℕ} [NeZero d]
    (f : MatrixAssignment Double.Generator d) {CH CN CS : ℝ}
    (hCH : 0 ≤ CH) (hCN : 0 ≤ CN) (hCS : 0 ≤ CS)
    (hCHsmall : 60 * CH ≤ (2 : ℝ) ^ 230) (hCNsmall : 60 * CN ≤ (2 : ℝ) ^ 230)
    (hCSsmall : 144 * CS ≤ (2 : ℝ) ^ 230)
    (hf : IsApproxRepresentation Double.relators paperExplicitDefect f)
    (hH : FiniteMatrixWeakGap
      (finiteNoDriftRootTuple (finiteNoDriftDoubleCopy f false) finiteNoDriftPositiveCoefficient)
      (1 / 60) (CH * paperExplicitDefect))
    (hN : FiniteMatrixWeakGap
      (finiteNoDriftRootTuple (finiteNoDriftDoubleCopy f false) finiteNoDriftCoefficient)
      (1 / 60) (CN * paperExplicitDefect))
    (hS : FiniteMatrixWeakGap (finiteNoDriftShearTuple (finiteNoDriftDoubleCopy f false))
      (1 / 144) (CS * paperExplicitDefect)) :
    unitaryLength (f (FreeGroup.mk Double.obstructionWord)) < 1 / 4 := by
  obtain ⟨A, D, hE⟩ := finiteNoDrift_explicit_energy_certificates (finiteNoDriftDoubleCopy f false)
    hCH hCN hCS hCHsmall hCNsmall hCSsmall paperExplicitDefect_pos.le le_rfl
    (finiteNoDrift_copy_model f hf false) hH hN hS
  exact finiteNoDrift_double_obstruction f A D (by unfold finiteALTExplicitTolerance; positivity)
    (by simp only [finiteALTExplicitTolerance, one_div, inv_pow]; exact le_rfl)
    paperExplicitDefect_pos.le finiteNoDrift_paper_defect_small hf hE

/-- The only inputs remaining here are the root H/N and shear S spectral certificates.
The error constants can vary with the represented matrices, within the displayed budget. -/
theorem finiteNoDrift_paper_double_bound_of_weakGaps
    (hgap : ∀ d : ℕ, ∀ [NeZero d], ∀ f : MatrixAssignment Double.Generator d,
      IsApproxRepresentation Double.relators paperExplicitDefect f →
      ∃ CH CN CS : ℝ, 0 ≤ CH ∧ 0 ≤ CN ∧ 0 ≤ CS ∧
        60 * CH ≤ (2 : ℝ) ^ 230 ∧ 60 * CN ≤ (2 : ℝ) ^ 230 ∧ 144 * CS ≤ (2 : ℝ) ^ 230 ∧
        FiniteMatrixWeakGap
          (finiteNoDriftRootTuple (finiteNoDriftDoubleCopy f false) finiteNoDriftPositiveCoefficient)
          (1 / 60) (CH * paperExplicitDefect) ∧
        FiniteMatrixWeakGap
          (finiteNoDriftRootTuple (finiteNoDriftDoubleCopy f false) finiteNoDriftCoefficient)
          (1 / 60) (CN * paperExplicitDefect) ∧
        FiniteMatrixWeakGap (finiteNoDriftShearTuple (finiteNoDriftDoubleCopy f false))
          (1 / 144) (CS * paperExplicitDefect)) : PaperExplicitDoubleBound := by
  intro d hd f hf
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  obtain ⟨CH, CN, CS, hCH, hCN, hCS, hCHsmall, hCNsmall, hCSsmall, hH, hN, hS⟩ := hgap d f hf
  exact (finiteNoDrift_explicit_double_of_weakGaps f hCH hCN hCS hCHsmall hCNsmall hCSsmall hf hH hN hS).le

end ThomGame.Analysis
