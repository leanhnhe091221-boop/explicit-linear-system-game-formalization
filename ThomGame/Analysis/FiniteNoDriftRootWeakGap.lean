module

public import ThomGame.Analysis.CompressorRootWeakGap
public import ThomGame.Analysis.FiniteNoDriftRootNormalization
public import ThomGame.Analysis.FiniteUCPWeakGapHeat
public import ThomGame.Analysis.FiniteNoDriftDouble

/-! Quantitative H and N weak gaps for the actual compressor and double tuples. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open scoped BigOperators
variable {d r : ℕ} [NeZero d]

theorem compressorRootTuple_weakGap (f : MatrixAssignment Compressor.Generator d)
    (σ : Fin r → Compressor.Coeff) (hr : r ≤ 7) {δ : ℝ} (hδ : 0 ≤ δ)
    (hf : IsApproxRepresentation Compressor.relators δ f) :
    FiniteMatrixWeakGap (finiteNoDriftRootTuple (fun s => f (FreeGroup.of s)) σ)
      (1/60) (10000000000*δ) := by
  intro X hX
  have hh := compressorRoot_laplacian_weak_gap f σ hr hδ hf X hX
  rw [finiteNoDrift_root_energy_normalization, finiteNoDrift_root_defect_sq_normalization]
  change (1/60:ℝ) * ((1/6:ℝ) * (inner ℂ (finiteMatrixHilbertEquiv d X)
    (∑ c : Fin 3, (finiteMatrixHilbertEquiv d X -
      compressorRootAverage f (Compressor.cyclicRoot c) σ (finiteMatrixHilbertEquiv d X)))).re) ≤
    (1/36:ℝ) * ‖∑ c : Fin 3, (finiteMatrixHilbertEquiv d X -
      compressorRootAverage f (Compressor.cyclicRoot c) σ (finiteMatrixHilbertEquiv d X))‖ ^ 2 + _
  dsimp only at hh
  linarith

theorem finiteNoDrift_root_weakGap (f : Compressor.Generator → UnitaryMatrix d)
    (σ : Fin r → Compressor.Coeff) (hr : r ≤ 7) {δ : ℝ} (hδ : 0 ≤ δ)
    (hf : FiniteNoDriftCompressorModel f δ) :
    FiniteMatrixWeakGap (finiteNoDriftRootTuple f σ) (1/60) (10000000000*δ) := by
  have ha : IsApproxRepresentation Compressor.relators δ (FreeGroup.lift f) := by
    rintro _ ⟨w, hw, rfl⟩
    exact hf w hw
  simpa using compressorRootTuple_weakGap (FreeGroup.lift f) σ hr hδ ha

theorem finiteNoDrift_double_root_weakGap (f : MatrixAssignment Double.Generator d)
    (b : Bool) (σ : Fin r → Compressor.Coeff) (hr : r ≤ 7)
    {δ : ℝ} (hδ : 0 ≤ δ) (hf : IsApproxRepresentation Double.relators δ f) :
    FiniteMatrixWeakGap (finiteNoDriftRootTuple (finiteNoDriftDoubleCopy f b) σ)
      (1/60) (10000000000*δ) :=
  finiteNoDrift_root_weakGap _ σ hr hδ (finiteNoDrift_copy_model f hf b)

theorem finiteNoDrift_double_H_weakGap (f : MatrixAssignment Double.Generator d)
    (b : Bool) {δ : ℝ} (hδ : 0 ≤ δ) (hf : IsApproxRepresentation Double.relators δ f) :
    FiniteMatrixWeakGap
      (finiteNoDriftRootTuple (finiteNoDriftDoubleCopy f b) finiteNoDriftPositiveCoefficient)
      (1/60) (10000000000*δ) :=
  finiteNoDrift_double_root_weakGap f b _ (by decide) hδ hf

theorem finiteNoDrift_double_N_weakGap (f : MatrixAssignment Double.Generator d)
    (b : Bool) {δ : ℝ} (hδ : 0 ≤ δ) (hf : IsApproxRepresentation Double.relators δ f) :
    FiniteMatrixWeakGap
      (finiteNoDriftRootTuple (finiteNoDriftDoubleCopy f b) finiteNoDriftCoefficient)
      (1/60) (10000000000*δ) :=
  finiteNoDrift_double_root_weakGap f b _ (by decide) hδ hf

end ThomGame.Analysis
