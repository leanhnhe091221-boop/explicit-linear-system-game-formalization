module

public import ThomGame.Analysis.FiniteUCPHeatBounds
public import ThomGame.Analysis.FiniteUCPALTDecomposition
public import ThomGame.Analysis.MatrixALTRefinement
public import ThomGame.Analysis.MatrixNonzeroScalarPartition
public import ThomGame.Analysis.MatrixALTFiniteReconstruction
public import ThomGame.Analysis.MatrixMarkovCompletelyPositive
public import ThomGame.Analysis.MatrixMarkovBimodule
public import ThomGame.Analysis.MatrixMarkovPerturbation
public import ThomGame.Analysis.MatrixMarkovDuplication
public import Mathlib.Algebra.Order.Chebyshev

/-!
# A finite ALT conclusion with explicit scalar conditions

The conditions concern only the finite parameters and can be checked without
any dimension-dependent choices. The projection partition, corrected channel,
and approximating algebra are constructed in the proof.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra

variable {d h : ℕ} [NeZero d] [NeZero h]

theorem finiteUCP_corrected_markov_distance (U : Fin h → UnitaryMatrix d)
    {κ η a : ℝ} (dec : MatrixALTDecomposition U κ η) (ha : 0 ≤ a)
    (hedit : altPrunedEditBound κ η ≤ 2 * a ^ 2) :
    matrixMixedNorm (matrixLazyMarkov dec.T - matrixLazyMarkov U) ≤ a := by
  have hh : (0 : ℝ) < h := Nat.cast_pos.mpr (NeZero.pos h)
  have hsum := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
    (f := fun j => hsNorm ((dec.T j).val - (Fin.append U U j).val))
  simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_add] at hsum
  have he := mul_le_mul_of_nonneg_left dec.perturbation (show 0 ≤ (h : ℝ) + h by positivity)
  have he' := mul_le_mul_of_nonneg_left hedit (show 0 ≤ 2 * (h : ℝ) ^ 2 by positivity)
  have hsum' : (∑ j, hsNorm ((dec.T j).val - (Fin.append U U j).val)) ^ 2 ≤
      (2 * (h : ℝ) * a) ^ 2 := by nlinarith only [hsum, he, he']
  have hb : (∑ j, hsNorm ((dec.T j).val - (Fin.append U U j).val)) ≤ 2 * (h : ℝ) * a :=
    (sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => hsNorm_nonneg _)) (by positivity)).mp hsum'
  have hw : 4 * lazyMarkovWeight (h + h) * (2 * (h : ℝ) * a) = a := by
    have he := lazyMarkovWeight_mul_card (h + h)
    simp only [Nat.cast_add] at he
    calc
      _ = 4 * (lazyMarkovWeight (h + h) * ((h : ℝ) + h)) * a := by ring
      _ = a := by rw [he]; ring
  have hbound : 4 * lazyMarkovWeight (h + h) *
      (∑ j, hsNorm ((dec.T j).val - (Fin.append U U j).val)) ≤ a := by
    exact (mul_le_mul_of_nonneg_left hb
      (mul_nonneg (by norm_num) (lazyMarkovWeight_nonneg (h + h)))).trans_eq hw
  rw [← matrixLazyMarkov_append_self U]
  apply matrixMixedNorm_le _ a ha
  intro X
  exact (matrixLazyMarkov_sub_hsNorm_le dec.T (Fin.append U U) X).trans
    (mul_le_mul_of_nonneg_right hbound (norm_nonneg X))

theorem finiteUCP_power_sub_hsNorm_le {k : ℕ} [NeZero k]
    (U : Fin h → UnitaryMatrix d) (V : Fin k → UnitaryMatrix d)
    (a : ℝ) (ha : 0 ≤ a)
    (hstep : ∀ X, hsNorm (matrixLazyMarkov U X - matrixLazyMarkov V X) ≤ a * matrixOpNorm X)
    (n : ℕ) (X : CMatrix d) :
    hsNorm ((matrixLazyMarkov U ^ n) X - (matrixLazyMarkov V ^ n) X) ≤
      (n : ℝ) * a * matrixOpNorm X := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : (matrixLazyMarkov U ^ (n + 1)) X - (matrixLazyMarkov V ^ (n + 1)) X =
        matrixLazyMarkov U ((matrixLazyMarkov U ^ n) X - (matrixLazyMarkov V ^ n) X) +
        (matrixLazyMarkov U ((matrixLazyMarkov V ^ n) X) - matrixLazyMarkov V ((matrixLazyMarkov V ^ n) X)) := by
      simp only [pow_succ', Module.End.mul_apply, map_sub]
      abel
    rw [he]
    calc
      _ ≤ hsNorm (matrixLazyMarkov U ((matrixLazyMarkov U ^ n) X - (matrixLazyMarkov V ^ n) X)) +
          hsNorm (matrixLazyMarkov U ((matrixLazyMarkov V ^ n) X) - matrixLazyMarkov V ((matrixLazyMarkov V ^ n) X)) :=
        hsNorm_add_le _ _
      _ ≤ (n : ℝ) * a * matrixOpNorm X + a * matrixOpNorm ((matrixLazyMarkov V ^ n) X) :=
        add_le_add ((matrixLazyMarkov_hsNorm_le U _).trans ih) (hstep _)
      _ ≤ (n : ℝ) * a * matrixOpNorm X + a * matrixOpNorm X :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (matrixLazyMarkov_pow_matrixOpNorm_le V n X) ha)
      _ = _ := by rw [Nat.cast_add, Nat.cast_one]; ring

theorem finiteUCP_corrected_power_idempotence (U : Fin h → UnitaryMatrix d)
    (Φ : CMatrix d →ₗ[ℂ] CMatrix d) {κ β a : ℝ}
    (hcontrol : FiniteUCPDefectControl U Φ κ β)
    {k : ℕ} [NeZero k] (V : Fin k → UnitaryMatrix d) (ha : 0 ≤ a)
    (hstep : matrixMixedNorm (matrixLazyMarkov V - matrixLazyMarkov U) ≤ a)
    (n : ℕ) (hn : 0 < n) :
    matrixMixedNorm ((matrixLazyMarkov V ^ n).comp (matrixLazyMarkov V ^ n) -
      matrixLazyMarkov V ^ n) ≤
        3 * (n : ℝ) * a + 2 * (Real.sqrt κ)⁻¹ * (Real.sqrt (n : ℝ))⁻¹ + ((n : ℝ) + 2) * β := by
  have hβ := hcontrol.beta_nonneg
  have hpower (m : ℕ) (X : CMatrix d) :
      hsNorm ((matrixLazyMarkov V ^ m) X - (matrixLazyMarkov U ^ m) X) ≤
        (m : ℝ) * a * matrixOpNorm X := by
    exact finiteUCP_power_sub_hsNorm_le V U a ha
      (fun Y => (hsNorm_apply_le_matrixMixedNorm (matrixLazyMarkov V - matrixLazyMarkov U) Y).trans
        (mul_le_mul_of_nonneg_right hstep (norm_nonneg Y))) m X
  have hbase := finiteUCP_matrixPower_idempotence U Φ hcontrol n hn
  apply matrixMixedNorm_le_of_unit_bound _ _ (by positivity)
  intro X hX
  have h0 := (hpower n X).trans (mul_le_of_le_one_right (by positivity) hX)
  have h1 := (hpower n ((matrixLazyMarkov U ^ n) X)).trans
    (mul_le_of_le_one_right (by positivity) ((matrixLazyMarkov_pow_matrixOpNorm_le U n X).trans hX))
  have h2 := (matrixLazyMarkov_pow_hsNorm_le V n
    ((matrixLazyMarkov V ^ n) X - (matrixLazyMarkov U ^ n) X)).trans h0
  have h3 := (hsNorm_apply_le_matrixMixedNorm
    ((matrixLazyMarkov U ^ n).comp (matrixLazyMarkov U ^ n) - matrixLazyMarkov U ^ n) X).trans
      ((mul_le_mul_of_nonneg_right hbase (norm_nonneg X)).trans
        (mul_le_of_le_one_right (by positivity) hX))
  have he : (matrixLazyMarkov V ^ n) ((matrixLazyMarkov V ^ n) X) - (matrixLazyMarkov V ^ n) X =
      (matrixLazyMarkov V ^ n) ((matrixLazyMarkov V ^ n) X - (matrixLazyMarkov U ^ n) X) +
      ((matrixLazyMarkov V ^ n) ((matrixLazyMarkov U ^ n) X) -
        (matrixLazyMarkov U ^ n) ((matrixLazyMarkov U ^ n) X)) +
      ((matrixLazyMarkov U ^ n) ((matrixLazyMarkov U ^ n) X) - (matrixLazyMarkov U ^ n) X) +
      ((matrixLazyMarkov U ^ n) X - (matrixLazyMarkov V ^ n) X) := by
    rw [map_sub]
    abel
  change hsNorm ((matrixLazyMarkov V ^ n) ((matrixLazyMarkov V ^ n) X) -
    (matrixLazyMarkov V ^ n) X) ≤ _
  rw [he]
  have hlast : hsNorm ((matrixLazyMarkov U ^ n) X - (matrixLazyMarkov V ^ n) X) ≤ (n : ℝ) * a := by
    simpa only [hsNorm_sub_comm] using h0
  have ht := hsNorm_add_le
    ((matrixLazyMarkov V ^ n) ((matrixLazyMarkov V ^ n) X - (matrixLazyMarkov U ^ n) X) +
      ((matrixLazyMarkov V ^ n) ((matrixLazyMarkov U ^ n) X) -
        (matrixLazyMarkov U ^ n) ((matrixLazyMarkov U ^ n) X)) +
      ((matrixLazyMarkov U ^ n) ((matrixLazyMarkov U ^ n) X) - (matrixLazyMarkov U ^ n) X))
    ((matrixLazyMarkov U ^ n) X - (matrixLazyMarkov V ^ n) X)
  have ht2 := hsNorm_add_le
    ((matrixLazyMarkov V ^ n) ((matrixLazyMarkov V ^ n) X - (matrixLazyMarkov U ^ n) X) +
      ((matrixLazyMarkov V ^ n) ((matrixLazyMarkov U ^ n) X) -
        (matrixLazyMarkov U ^ n) ((matrixLazyMarkov U ^ n) X)))
    ((matrixLazyMarkov U ^ n) ((matrixLazyMarkov U ^ n) X) - (matrixLazyMarkov U ^ n) X)
  have ht1 := hsNorm_add_le
    ((matrixLazyMarkov V ^ n) ((matrixLazyMarkov V ^ n) X - (matrixLazyMarkov U ^ n) X))
    ((matrixLazyMarkov V ^ n) ((matrixLazyMarkov U ^ n) X) -
      (matrixLazyMarkov U ^ n) ((matrixLazyMarkov U ^ n) X))
  change hsNorm ((matrixLazyMarkov U ^ n) ((matrixLazyMarkov U ^ n) X) -
    (matrixLazyMarkov U ^ n) X) ≤ _ at h3
  linarith

/-- A finite ALT conclusion from the two smoothing estimates. Every additional
hypothesis is an explicit scalar inequality in the chosen parameters. -/
theorem exists_finiteUCP_ALT_algebra (U : Fin h → UnitaryMatrix d)
    (Φ : CMatrix d →CP CMatrix d)
    (htrace : ∀ X, normalizedTrace (Φ X) = normalizedTrace X)
    {κ α β η a ρ τ : ℝ} (n : ℕ) (hn : 0 < n)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hα : 0 < α)
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hηκ : η ≤ κ / 1024)
    (hsmall : (1 + 61440 / (κ * Real.sqrt κ)) * η ≤ 1)
    (hαη : α ≤ η ^ 4) (hexp : 9 * α ≤ Real.exp (-(η ^ 4)⁻¹))
    (hcontrol : FiniteUCPDefectControl U Φ.toLinearMap κ β)
    (hβα : β ≤ α ^ 2 / 64)
    (ha : 0 ≤ a) (hedit : altPrunedEditBound κ η ≤ 2 * a ^ 2)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1 / 1024)
    (hscalar : (1 - κ ^ 2 / (2 : ℝ) ^ 28) ^ n ≤ ρ ^ 4)
    (hidem : 3 * (n : ℝ) * a + 2 * (Real.sqrt κ)⁻¹ * (Real.sqrt (n : ℝ))⁻¹ +
      ((n : ℝ) + 2) * β ≤ ρ ^ 4)
    (hdistance : 134 * Real.sqrt ρ + (n : ℝ) * a + ((n : ℝ) + 2) * β ≤ τ)
    (henergy : 2 * ((Real.sqrt (n : ℝ))⁻¹ + 134 * Real.sqrt ρ + (n : ℝ) * a) ≤ τ) :
    ∃ A : StarSubalgebra ℂ (CMatrix d),
      matrixMixedNorm (matrixTraceProjection A - matrixLazyMarkov U ^ n) ≤
        134 * Real.sqrt ρ + (n : ℝ) * a ∧
      (∀ X, matrixOpNorm X ≤ 1 → hsNorm (X - matrixTraceProjection A X) ≤
        2 * (Real.sqrt κ)⁻¹ * Real.sqrt (matrixCoordinateEnergy U X) + τ) ∧
      (∀ X ∈ A, matrixOpNorm X ≤ 1 → Real.sqrt (matrixCoordinateEnergy U X) ≤ τ) := by
  obtain ⟨pruned⟩ := exists_finiteUCP_ALT_prunedDecomposition U Φ htrace
    hκ hκ1 hα hη hη8 hηκ hsmall hαη hexp hcontrol hβα
  obtain ⟨dec⟩ := exists_matrixALT_refinement U pruned
  obtain ⟨Q, hQne, _, _⟩ := dec.partition.exists_nonzero dec.T
  have hstep := finiteUCP_corrected_markov_distance U dec ha hedit
  let F := matrixMarkovPowerCP dec.T n
  have hg1 : κ ^ 2 / (2 : ℝ) ^ 28 ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hs : κ ^ 2 ≤ 1 := by nlinarith [hκ.le, hκ1]
    exact hs.trans (by norm_num)
  have hmix : matrixScalarMixingError Q.E F.toLinearMap ≤ ρ ^ 4 := by
    change matrixScalarCornerError Q n ≤ ρ ^ 4
    exact (Q.scalarCornerError_le hg1 hQne n).trans hscalar
  have hidem' : matrixMixedNorm (F.toLinearMap.comp F.toLinearMap - F.toLinearMap) ≤ ρ ^ 4 :=
    (finiteUCP_corrected_power_idempotence U Φ.toLinearMap hcontrol dec.T ha hstep n hn).trans hidem
  obtain ⟨A, _, hA⟩ := exists_matrixALT_approximating_algebra F
    (matrixLazyMarkov_pow_one dec.T n) (matrixLazyMarkov_pow_trace dec.T n)
    (matrixLazyMarkov_pow_pairing dec.T n) Q.E Q.projection hQne Q.orthogonal Q.sum_one
    (Q.markov_pow_bimodule n) ρ hρ hρsmall hmix hidem'
  have hpower (X : CMatrix d) (hX : matrixOpNorm X ≤ 1) :
      hsNorm ((matrixLazyMarkov dec.T ^ n) X - (matrixLazyMarkov U ^ n) X) ≤ (n : ℝ) * a := by
    have he := finiteUCP_power_sub_hsNorm_le dec.T U a ha
      (fun Y => (hsNorm_apply_le_matrixMixedNorm (matrixLazyMarkov dec.T - matrixLazyMarkov U) Y).trans
        (mul_le_mul_of_nonneg_right hstep (norm_nonneg Y))) n X
    exact he.trans (mul_le_of_le_one_right (by positivity) hX)
  have happrox (X : CMatrix d) (hX : matrixOpNorm X ≤ 1) :
      hsNorm (matrixTraceProjection A X - (matrixLazyMarkov U ^ n) X) ≤
        134 * Real.sqrt ρ + (n : ℝ) * a := by
    have he := (hsNorm_apply_le_matrixMixedNorm (F.toLinearMap - matrixTraceProjection A) X).trans
      ((mul_le_mul_of_nonneg_right hA (norm_nonneg X)).trans (mul_le_of_le_one_right (by positivity) hX))
    change hsNorm ((matrixLazyMarkov dec.T ^ n) X - matrixTraceProjection A X) ≤ _ at he
    have hdecomp : matrixTraceProjection A X - (matrixLazyMarkov U ^ n) X =
        (matrixTraceProjection A X - (matrixLazyMarkov dec.T ^ n) X) +
          ((matrixLazyMarkov dec.T ^ n) X - (matrixLazyMarkov U ^ n) X) := by abel
    rw [hdecomp]
    exact (hsNorm_add_le _ _).trans (add_le_add (by simpa only [hsNorm_sub_comm] using he) (hpower X hX))
  refine ⟨A, matrixMixedNorm_le_of_unit_bound _ _ (by positivity) happrox, ?_, ?_⟩
  · intro X hX
    have hdist := finiteUCP_matrixPower_distance U Φ.toLinearMap hcontrol n X hX
    have happ := happrox X hX
    have he : X - matrixTraceProjection A X =
        (X - (matrixLazyMarkov U ^ n) X) + ((matrixLazyMarkov U ^ n) X - matrixTraceProjection A X) := by abel
    rw [he]
    have ht := hsNorm_add_le (X - (matrixLazyMarkov U ^ n) X)
      ((matrixLazyMarkov U ^ n) X - matrixTraceProjection A X)
    rw [hsNorm_sub_comm ((matrixLazyMarkov U ^ n) X) (matrixTraceProjection A X)] at ht
    linarith
  · intro X hXA hX
    have happ := happrox X hX
    rw [matrixTraceProjection_eq_self A X hXA] at happ
    have he := finiteUCP_energy_sqrt_transfer U X ((matrixLazyMarkov U ^ n) X)
    have hheat := finiteUCP_matrixPower_energy_sqrt_bound U n hn X hX
    linarith

end ThomGame.Analysis
