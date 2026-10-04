module

public import ThomGame.Analysis.MatrixSpectralCoarea
public import ThomGame.Analysis.MatrixSpectralActiveMass

/-!
# Spectral coarea for finite families of positive matrices

The active spectral mass is at most the total normalized trace divided
by `2a`. This proves the family inequality in ALT Lemma 2.3 for actual
spectral projections, as well as existence of a common threshold.
-/

@[expose] public section
namespace ThomGame.Analysis

open MeasureTheory Set
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {d h : Nat} {ι : Type*} [Fintype ι]

theorem matrixFamilySpectralCut_energy_intervalIntegrable (X : ι → CMatrix d)
    (hX : ∀ k, Matrix.IsHermitian (X k)) (U : Fin h → UnitaryMatrix d) (a b : ℝ) :
    IntervalIntegrable (fun s => ∑ k, matrixCoordinateEnergy U (matrixSpectralCut (X k) s))
      volume a b := by
  have he : (fun s => ∑ k, matrixCoordinateEnergy U (matrixSpectralCut (X k) s)) =
      ∑ k, (fun s => matrixCoordinateEnergy U (matrixSpectralCut (X k) s)) := by
    funext s
    simp only [Finset.sum_apply]
  rw [he]
  exact IntervalIntegrable.sum Finset.univ fun k _ =>
    matrixSpectralCut_energy_intervalIntegrable (hX k) U a b

variable [NeZero h]

theorem matrixFamilySpectralCut_coarea (X : ι → CMatrix d) (hX : ∀ k, (X k).PosSemidef)
    (U : Fin h → UnitaryMatrix d) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ s in a..b, ∑ k, matrixCoordinateEnergy U (matrixSpectralCut (X k) s)) ≤
      Real.sqrt (((∑ k, (normalizedTrace (X k)).re) / (2 * a)) * ∑ k, matrixCoordinateEnergy U (X k)) := by
  have hM : (∑ p : ι × (Fin d × Fin d), spectralActiveWeight a
      (matrixEnergyWeight (matrixEigenbasisTuple (hX p.1).isHermitian U) p.2.1 p.2.2)
      ((hX p.1).isHermitian.eigenvalues p.2.1) ((hX p.1).isHermitian.eigenvalues p.2.2)) ≤
      (∑ k, (normalizedTrace (X k)).re) / (2 * a) := by
    simp only [Fintype.sum_prod_type]
    calc
      _ ≤ ∑ k, (normalizedTrace (X k)).re / (2 * a) :=
        Finset.sum_le_sum fun k _ => matrixSpectralActiveMass_le (hX k) U a ha
      _ = _ := by rw [Finset.sum_div]
  have he := weighted_spectralStep_coarea_of_mass_le a b hab
    (fun p : ι × (Fin d × Fin d) => matrixEnergyWeight (matrixEigenbasisTuple (hX p.1).isHermitian U) p.2.1 p.2.2)
    (fun p => (hX p.1).isHermitian.eigenvalues p.2.1)
    (fun p => (hX p.1).isHermitian.eigenvalues p.2.2)
    (fun p => matrixEnergyWeight_nonneg _ _ _) _ hM
  simpa only [Fintype.sum_prod_type, matrixSpectralCut_energy (hX _).isHermitian,
    matrixCoordinateEnergy_spectral (hX _).isHermitian] using he

theorem exists_matrixFamilySpectralCut_energy_le (X : ι → CMatrix d) (hX : ∀ k, (X k).PosSemidef)
    (U : Fin h → UnitaryMatrix d) (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ s ∈ Icc a b, (∑ k, matrixCoordinateEnergy U (matrixSpectralCut (X k) s)) ≤
      Real.sqrt (((∑ k, (normalizedTrace (X k)).re) / (2 * a)) * ∑ k, matrixCoordinateEnergy U (X k)) / (b - a) := by
  obtain ⟨s, hs, hse⟩ := exists_le_intervalIntegral_average hab
    (matrixFamilySpectralCut_energy_intervalIntegrable X (fun k => (hX k).isHermitian) U a b)
  exact ⟨s, hs, hse.trans (div_le_div_of_nonneg_right
    (matrixFamilySpectralCut_coarea X hX U a b ha hab.le) (sub_nonneg.mpr hab.le))⟩

noncomputable def matrixSpectralInterval (X : CMatrix d) (a b : ℝ) : CMatrix d :=
  cfc (fun t : ℝ => if a ≤ t ∧ t ≤ b then 1 else 0) X

theorem matrixSpectralInterval_one_eq_cut {X : CMatrix d} (hX : Matrix.IsHermitian X)
    (hX₁ : X ≤ 1) (s : ℝ) : matrixSpectralInterval X s 1 = matrixSpectralCut X s := by
  apply cfc_congr
  intro t ht
  have ht₁ : t ≤ 1 := (CFC.le_one_iff (R := ℝ) X hX.isSelfAdjoint).1 hX₁ t ht
  simp only [ht₁, and_true, spectralStep]

theorem matrixFamilySpectralInterval_coarea (X : ι → CMatrix d)
    (hX₀ : ∀ k, 0 ≤ X k) (hX₁ : ∀ k, X k ≤ 1)
    (U : Fin h → UnitaryMatrix d) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ s in a..b, ∑ k, matrixCoordinateEnergy U (matrixSpectralInterval (X k) s 1)) ≤
      Real.sqrt (((∑ k, (normalizedTrace (X k)).re) / (2 * a)) * ∑ k, matrixCoordinateEnergy U (X k)) := by
  have hp (k : ι) : (X k).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (hX₀ k)
  simp only [matrixSpectralInterval_one_eq_cut (hp _).isHermitian (hX₁ _)]
  exact matrixFamilySpectralCut_coarea X hp U a b ha hab

theorem exists_matrixFamilySpectralInterval_energy_le (X : ι → CMatrix d)
    (hX₀ : ∀ k, 0 ≤ X k) (hX₁ : ∀ k, X k ≤ 1)
    (U : Fin h → UnitaryMatrix d) (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ s ∈ Icc a b, (∑ k, matrixCoordinateEnergy U (matrixSpectralInterval (X k) s 1)) ≤
      Real.sqrt (((∑ k, (normalizedTrace (X k)).re) / (2 * a)) * ∑ k, matrixCoordinateEnergy U (X k)) / (b - a) := by
  have hp (k : ι) : (X k).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (hX₀ k)
  simp only [matrixSpectralInterval_one_eq_cut (hp _).isHermitian (hX₁ _)]
  exact exists_matrixFamilySpectralCut_energy_le X hp U a b ha hab

end ThomGame.Analysis
