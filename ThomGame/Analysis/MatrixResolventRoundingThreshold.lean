module

public import ThomGame.Analysis.MatrixResolventRoundedCoverage
public import ThomGame.Analysis.MatrixFamilySpectralCoarea

/-!
# A common threshold for resolvent rounding

The actual family has total trace at most one. Coarea chooses one
threshold giving all rank, weighted-trace and coverage conclusions,
with energy controlled by the actual sum of resolvent-difference
energies. The input-energy estimate is proved in MatrixResolventFamilyEnergy;
MatrixResolventSmallEnergyFamily uses it to complete ALT Lemma 3.3.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {d h : Nat} [NeZero d] [NeZero h] {γ : ℝ} {P : CMatrix d}

theorem matrixResolventDifferenceFamily_trace_sum_le_one {lam : ℝ} (hlam : 0 < lam)
    (hP : IsStarProjection P) (F : Nat → CMatrix d) (hF : ∀ i, IsStarProjection (F i)) (n : Nat) :
    (∑ i : Fin n, (normalizedTrace (matrixResolventDifferenceFamily lam P F i)).re) ≤ 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (normalizedTrace (matrixResolventDifferenceFamily lam P F i)).re)]
  have he := normalizedTrace_re_mono (matrixResolventDifferenceFamily_sum_le_one hlam hP.nonneg F hF n)
  rw [normalizedTrace_one, Complex.one_re] at he
  simpa only [normalizedTrace, Matrix.trace_sum, Finset.sum_div, Complex.re_sum] using he

theorem exists_matrixResolventRounding_energy_le (hγ : 0 < γ) (hP : IsStarProjection P)
    (F : Nat → CMatrix d) (hF : ∀ i, IsStarProjection (F i)) (n : Nat)
    (U : Fin h → UnitaryMatrix d) :
    ∃ s ∈ Set.Icc γ (2 * γ),
      (∑ i : Fin n, matrixCoordinateEnergy U (matrixResolventSpectralProjection (γ ^ 2) P F s i)) ≤
        Real.sqrt ((∑ i : Fin n, matrixCoordinateEnergy U
          (matrixResolventDifferenceFamily (γ ^ 2) P F i)) / (2 * γ)) / γ := by
  let D : Fin n → CMatrix d := fun i => matrixResolventDifferenceFamily (γ ^ 2) P F i
  have hD (i : Fin n) : (D i).PosSemidef := Matrix.nonneg_iff_posSemidef.mp
    (matrixResolventDifferenceFamily_nonneg (sq_pos_of_pos hγ) hP.nonneg F hF i)
  obtain ⟨s, hs, hse⟩ := exists_matrixFamilySpectralCut_energy_le D hD U γ (2 * γ) hγ (by linarith)
  have htrace : (∑ i, (normalizedTrace (D i)).re) ≤ 1 :=
    matrixResolventDifferenceFamily_trace_sum_le_one (sq_pos_of_pos hγ) hP F hF n
  have henergy : 0 ≤ ∑ i, matrixCoordinateEnergy U (D i) :=
    Finset.sum_nonneg fun i _ => matrixCoordinateEnergy_nonneg U (D i)
  refine ⟨s, hs, hse.trans ?_⟩
  have hden : 2 * γ - γ = γ := by ring
  rw [hden]
  apply div_le_div_of_nonneg_right _ hγ.le
  apply Real.sqrt_le_sqrt
  calc
    _ ≤ (1 / (2 * γ)) * ∑ i, matrixCoordinateEnergy U (D i) :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right htrace (by positivity)) henergy
    _ = _ := by simp only [div_eq_mul_inv]; ring

theorem exists_matrixResolventSpectralRounding (hγ : 0 < γ) (hP : IsStarProjection P)
    (F : Nat → CMatrix d) (hF : ∀ i, IsStarProjection (F i)) (n : Nat)
    (htrace : (∑ i ∈ Finset.range n, (normalizedTrace (F i)).re) ≤ 3)
    (U : Fin h → UnitaryMatrix d) :
    ∃ s ∈ Set.Icc γ (2 * γ),
      (∀ i : Fin n, IsStarProjection (matrixResolventSpectralProjection (γ ^ 2) P F s i) ∧
        (matrixResolventSpectralProjection (γ ^ 2) P F s i).rank ≤ (F i).rank) ∧
      (∑ i : Fin n, (normalizedTrace (matrixProjectionPartialSum P F i ^ 2 *
        matrixResolventSpectralProjection (γ ^ 2) P F s i)).re) ≤ 3 * γ ∧
      matrixFamilyCoverageDefect (fun i : Fin n => matrixResolventSpectralProjection (γ ^ 2) P F s i) ≤
        (normalizedTrace P).re +
        (normalizedTrace (1 - matrixSpectralCut (matrixProjectionPartialSum P F n) γ)).re + 7 * γ ∧
      (∑ i : Fin n, matrixCoordinateEnergy U (matrixResolventSpectralProjection (γ ^ 2) P F s i)) ≤
        Real.sqrt ((∑ i : Fin n, matrixCoordinateEnergy U
          (matrixResolventDifferenceFamily (γ ^ 2) P F i)) / (2 * γ)) / γ := by
  obtain ⟨s, hs, he⟩ := exists_matrixResolventRounding_energy_le hγ hP F hF n U
  refine ⟨s, hs, ?_, matrixResolventSpectralProjection_weighted_gamma_le hγ hP F hF n htrace hs,
    matrixResolventSpectralProjection_coverage hγ hP F hF n htrace hs, he⟩
  intro i
  exact ⟨matrixResolventSpectralProjection_isStarProjection (sq_pos_of_pos hγ) hP.nonneg F hF s i,
    matrixResolventSpectralProjection_rank_le (sq_pos_of_pos hγ) hP.nonneg F hF (hγ.trans_le hs.1) i⟩

end ThomGame.Analysis
