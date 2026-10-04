module

public import ThomGame.Analysis.FiniteNoDriftRecovery

/-! Four finite energy certificates imply the original no-drift analytic inputs. -/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d]

structure FiniteNoDriftEnergyCertificates (f : Compressor.Generator → UnitaryMatrix d)
    (A D : StarSubalgebra ℂ (CMatrix d)) (τ : ℝ) : Prop where
  positive_distance : ∀ X, matrixOpNorm X ≤ 1 → hsNorm (X - matrixTraceProjection A X) ≤
    240 * Real.sqrt (matrixCoordinateEnergy (finiteNoDriftRootTuple f finiteNoDriftPositiveCoefficient) X) + τ
  positive_energy : ∀ X, X ∈ A → matrixOpNorm X ≤ 1 →
    Real.sqrt (matrixCoordinateEnergy (finiteNoDriftRootTuple f finiteNoDriftPositiveCoefficient) X) ≤ τ
  full_distance : ∀ X, matrixOpNorm X ≤ 1 → hsNorm (X - matrixTraceProjection D X) ≤
    1200 * Real.sqrt (matrixCoordinateEnergy (finiteNoDriftQTuple f) X) + τ
  full_energy : ∀ X, X ∈ D → matrixOpNorm X ≤ 1 →
    Real.sqrt (matrixCoordinateEnergy (finiteNoDriftQTuple f) X) ≤ τ

theorem finiteNoDrift_energy_near (f : Compressor.Generator → UnitaryMatrix d)
    (A D : StarSubalgebra ℂ (CMatrix d)) {τ : ℝ} (hτ : 0 ≤ τ)
    (E : FiniteNoDriftEnergyCertificates f A D τ) : MatrixNearInclusion D A (3841 * τ) := by
  intro X hXD hX
  have hQ := finiteNoDriftEnergy_sq_bound (finiteNoDriftQTuple f) X (E.full_energy X hXD hX)
  have hHN := finiteNoDrift_positive_energy_le f X
  have hS := matrixCoordinateEnergy_nonneg (finiteNoDriftShearTuple f) X
  rw [finiteNoDriftQEnergy] at hQ
  have hs := Real.sq_sqrt (matrixCoordinateEnergy_nonneg (finiteNoDriftRootTuple f finiteNoDriftPositiveCoefficient) X)
  have hh : Real.sqrt (matrixCoordinateEnergy (finiteNoDriftRootTuple f finiteNoDriftPositiveCoefficient) X) ≤ 16 * τ := by
    nlinarith [Real.sqrt_nonneg (matrixCoordinateEnergy (finiteNoDriftRootTuple f finiteNoDriftPositiveCoefficient) X)]
  refine ⟨matrixTraceProjection A X, matrixTraceProjection_mem A X, ?_⟩
  have he := E.positive_distance X hX
  linarith

theorem finiteNoDrift_energy_shear (f : Compressor.Generator → UnitaryMatrix d)
    (A D : StarSubalgebra ℂ (CMatrix d)) {τ : ℝ} (hτ : 0 ≤ τ)
    (E : FiniteNoDriftEnergyCertificates f A D τ) (j : Fin 6)
    (X : CMatrix d) (hXD : X ∈ D) (hX : matrixOpNorm X ≤ 1) :
    hsNorm (X * (finiteNoDriftShearTuple f j).val - (finiteNoDriftShearTuple f j).val * X) ≤ 7 * τ := by
  have hQ := finiteNoDriftEnergy_sq_bound (finiteNoDriftQTuple f) X (E.full_energy X hXD hX)
  have hN := matrixCoordinateEnergy_nonneg (finiteNoDriftRootTuple f finiteNoDriftCoefficient) X
  have hs := finiteNoDriftEnergy_single (finiteNoDriftShearTuple f) X j
  rw [finiteNoDriftQEnergy] at hQ
  rw [hsNorm_sub_comm]
  change finiteNoDriftComm (finiteNoDriftShearTuple f j) X ≤ 7 * τ
  norm_num only [Nat.cast_ofNat] at hs
  nlinarith [finiteNoDriftComm_nonneg (finiteNoDriftShearTuple f j) X]

theorem finiteNoDrift_pullback_contract (A : StarSubalgebra ℂ (CMatrix d)) (U : UnitaryMatrix d)
    (X : CMatrix d) (hXA : X ∈ matrixUnitaryPullbackAlgebra A U) (hX : matrixOpNorm X ≤ 1) :
    ∃ Y ∈ A, matrixOpNorm Y ≤ 1 ∧ U.valᴴ * Y * U.val = X := by
  let Y := (matrixUnitaryPullbackEquiv A U ⟨X, hXA⟩ : CMatrix d)
  have he : Y = U.val * X * U.valᴴ := matrixUnitaryPullbackEquiv_coe A U ⟨X, hXA⟩
  refine ⟨Y, (matrixUnitaryPullbackEquiv A U ⟨X, hXA⟩).property, ?_, ?_⟩
  · rw [he]
    have hn := finiteNoDrift_conjugation_contract U⁻¹ X hX
    change matrixOpNorm (U.valᴴᴴ * X * U.valᴴ) ≤ 1 at hn
    simpa only [Matrix.conjTranspose_conjTranspose] using hn
  · rw [he]
    have hu : U.valᴴ * U.val = 1 := U.prop.1
    calc
      _ = (U.valᴴ * U.val) * X * (U.valᴴ * U.val) := by simp only [mul_assoc]
      _ = X := by rw [hu, one_mul, mul_one]

theorem finiteNoDrift_energy_forward (f : Compressor.Generator → UnitaryMatrix d)
    (A D : StarSubalgebra ℂ (CMatrix d)) {τ δ : ℝ} (hτ : 0 ≤ τ) (hδ : 0 ≤ δ)
    (hf : FiniteNoDriftCompressorModel f δ) (E : FiniteNoDriftEnergyCertificates f A D τ) (j : Fin 6) :
    MatrixNearInclusion (matrixUnitaryPullbackAlgebra A (finiteNoDriftShearTuple f j)) A
      (2700000 * τ + 20000 * δ) := by
  intro X hXA hX
  obtain ⟨Y, hYA, hYn, hYX⟩ := finiteNoDrift_pullback_contract A (finiteNoDriftShearTuple f j) X hXA hX
  have hpos := finiteNoDrift_positive_comm f hf hδ hτ Y hYn (E.positive_energy Y hYA hYn)
  have he := finiteNoDrift_forward_energy f hf hδ (by positivity : 0 ≤ 350 * τ + 2 * δ) Y hYn hpos
    ((Fintype.equivFinOfCardEq Compressor.root_card).symm j)
  change Real.sqrt (matrixCoordinateEnergy (finiteNoDriftRootTuple f finiteNoDriftPositiveCoefficient)
    ((finiteNoDriftShearTuple f j).valᴴ * Y * (finiteNoDriftShearTuple f j).val)) ≤ _ at he
  rw [hYX] at he
  have hd := E.positive_distance X hX
  refine ⟨matrixTraceProjection A X, matrixTraceProjection_mem A X, ?_⟩
  linarith

theorem finiteNoDrift_energy_anchor (f : Compressor.Generator → UnitaryMatrix d)
    (A D : StarSubalgebra ℂ (CMatrix d)) {τ δ : ℝ} (hτ : 0 ≤ τ) (hδ : 0 ≤ δ)
    (hf : FiniteNoDriftCompressorModel f δ) (E : FiniteNoDriftEnergyCertificates f A D τ) :
    FiniteNoDriftAnchor A D (finiteNoDriftShearTuple f) (10 ^ 6) (6000000 * τ + 70000 * δ) := by
  intro X hXA _ hX b hb
  have hb0 : 0 ≤ b := (hsNorm_nonneg _).trans (hb 0)
  have hs (s : Compressor.Root) : finiteNoDriftComm (f (.inr s)) X ≤ b := by
    have he := hb ((Fintype.equivFinOfCardEq Compressor.root_card) s)
    rw [finiteNoDriftShearTuple_at, hsNorm_sub_comm] at he
    exact he
  have hpos := finiteNoDrift_positive_comm f hf hδ hτ X hX (E.positive_energy X hXA hX)
  have hQ := finiteNoDrift_Q_anchor_energy f hf hδ (by positivity : 0 ≤ 350 * τ + 2 * δ) hb0 X hX hpos hs
  have hd := E.full_distance X hX
  norm_num only [pow_succ, pow_zero] at hd ⊢
  linarith

theorem finiteNoDrift_energy_c_distance (f : Compressor.Generator → UnitaryMatrix d)
    (A D : StarSubalgebra ℂ (CMatrix d)) {τ δ : ℝ} (hδ : 0 ≤ δ)
    (E : FiniteNoDriftEnergyCertificates f A D τ) (C : UnitaryMatrix d)
    (hC : ∀ r m, Compressor.positive (.inl (r, m)) = true →
      finiteNoDriftComm (f (.inl (r, m))) C.val ≤ 2 * δ) :
    hsNorm (C.val - matrixTraceProjection A C.val) ≤ τ + 3840 * δ := by
  have hE := finiteNoDriftRootEnergy_max f finiteNoDriftPositiveCoefficient C.val
    (by positivity : 0 ≤ 2 * δ) (fun c i => hC _ _ (finiteNoDrift_positive_coeff i _))
  have hd := E.positive_distance C.val (matrixOpNorm_unitary_le C)
  norm_num only [Nat.reduceMul, Nat.cast_ofNat] at hE
  linarith

end ThomGame.Analysis
