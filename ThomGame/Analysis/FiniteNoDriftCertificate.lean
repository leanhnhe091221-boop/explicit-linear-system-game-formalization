module

public import ThomGame.Analysis.FiniteNoDriftFrameUnitary

/-! A fixed finite certificate at precision `10⁻⁴⁰` closes the no-drift obstruction. -/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

theorem finiteNoDrift_numeric {τ δ : ℝ} (hτ : 0 ≤ τ) (hτsmall : τ ≤ 1 / (10 : ℝ) ^ 40)
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / (10 : ℝ) ^ 40) :
    0 ≤ (2700000 * τ + 20000 * δ) + 200 * (3841 * τ) + 6 * (7 * τ) ∧
    (2700000 * τ + 20000 * δ) + 200 * (3841 * τ) + 6 * (7 * τ) ≤ 1 / (10 : ℝ) ^ 33 ∧
    (6000000 * τ + 70000 * δ) + 20 * (3841 * τ) +
      2 * (10 : ℝ) ^ 6 * (100 * (3841 * τ) + 3 * (7 * τ)) ≤ 1 / (10 : ℝ) ^ 27 ∧
    (τ + 3840 * δ) + 4 * (3841 * τ) ≤ 1 / 1000 ∧
    (350 * τ + 2 * δ) + 2 * (4 * (3841 * τ)) ≤ 1 / 1000 ∧
    3 * (7 * τ) + 96 * (3841 * τ) ≤ 1 / 1000 ∧
    3841 * τ ≤ 1 / 2 := by
  norm_num at hτsmall hδsmall ⊢
  constructor
  · positivity
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

variable {d : Nat} [NeZero d]

/-- The analytic part of the explicit obstruction.  The hypotheses are finite
certificates for the original algebras, before any stabilization or unitary correction. -/
theorem finiteNoDrift_finite_certificate
    (A₀ D₀ : StarSubalgebra ℂ (CMatrix d)) {h : Nat} (U : Fin h → UnitaryMatrix d)
    (j : Fin h) (V H : UnitaryMatrix d) {τ δ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ 1 / (10 : ℝ) ^ 40)
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / (10 : ℝ) ^ 40)
    (hDA : MatrixNearInclusion D₀ A₀ (3841 * τ))
    (hcomm : ∀ l X, X ∈ D₀ → matrixOpNorm X ≤ 1 →
      hsNorm (X * (U l).val - (U l).val * X) ≤ 7 * τ)
    (hforward : ∀ l, MatrixNearInclusion (matrixUnitaryPullbackAlgebra A₀ (U l)) A₀
      (2700000 * τ + 20000 * δ))
    (hanchor : FiniteNoDriftAnchor A₀ D₀ U ((10 : ℝ) ^ 6) (6000000 * τ + 70000 * δ))
    (hC : hsNorm (((U j)⁻¹ * V).val - matrixTraceProjection A₀ ((U j)⁻¹ * V).val) ≤ τ + 3840 * δ)
    (hH : ∀ X, X ∈ A₀ → matrixOpNorm X ≤ 1 → hsNorm (X * H.val - H.val * X) ≤ 350 * τ + 2 * δ) :
    hsNorm ((H * (V * (U j)⁻¹) * H⁻¹ * (V * (U j)⁻¹)⁻¹).val - 1) < 1 / 4 := by
  obtain ⟨n, hn, F, hF, A, D, R, hdn, hdim, hDA', hA, hA₀, hD, hD₀, hR, hUR, hf, ha⟩ :=
    finiteNoDrift_stabilize A₀ D₀ U (by positivity) (by positivity) (by positivity)
      hDA hcomm hforward hanchor
  letI : NeZero n := hn
  obtain ⟨hε0, hεsmall, hνsmall, hαsmall, hθsmall, hζsmall, hηsmall⟩ :=
    finiteNoDrift_numeric hτ hτsmall hδ hδsmall
  have hεhalf : (2700000 * τ + 20000 * δ) + 200 * (3841 * τ) + 6 * (7 * τ) < 1 / 2 :=
    hεsmall.trans_lt (by norm_num)
  have hrev := finiteNoDrift_reverse A D hDA' R hR hε0 hεhalf hf ha j
  have hrevsmall : MatrixNearInclusion A (matrixUnitaryPullbackAlgebra A (R j)) (1 / 1000) :=
    finiteNoDrift_near_mono hrev (finiteNoDriftError_small hε0 hεsmall hνsmall)
  let T' := finiteNoDriftFrameUnitary F hF (U j)
  let V' := finiteNoDriftFrameUnitary F hF V
  let H' := finiteNoDriftFrameUnitary F hF H
  have hCold : hsNorm ((T'⁻¹ * V').val -
      matrixTraceProjection (matrixFrameScalarAlgebra A₀ F hF) (T'⁻¹ * V').val) ≤ τ + 3840 * δ := by
    have he := (finiteNoDriftFrame_distance F hF hdn A₀ ((U j)⁻¹ * V).val 1).trans hC
    change hsNorm ((finiteNoDriftFrameUnitary F hF ((U j)⁻¹ * V)).val -
      matrixTraceProjection (matrixFrameScalarAlgebra A₀ F hF)
        (finiteNoDriftFrameUnitary F hF ((U j)⁻¹ * V)).val) ≤ _ at he
    simpa only [finiteNoDriftFrameUnitary_mul, finiteNoDriftFrameUnitary_inv] using he
  have hCnew := finiteNoDrift_distance_transfer (matrixFrameScalarAlgebra A₀ F hF) A
    (T'⁻¹ * V').val (matrixOpNorm_unitary_le _) hCold hA₀
  have hHold : ∀ X, X ∈ matrixFrameScalarAlgebra A₀ F hF → matrixOpNorm X ≤ 1 →
      hsNorm (X * H'.val - H'.val * X) ≤ 350 * τ + 2 * δ :=
    finiteNoDriftFrame_commutator_bound F hF hdn A₀ H hH
  have hHnew := finiteNoDrift_near_commutator_bound (matrixFrameScalarAlgebra A₀ F hF) A H' hA hHold
  have hw := finiteNoDrift_obstruction_word A (R j) T' V' H'
    hCnew hrevsmall (hUR j) hHnew
  have hwsmall : hsNorm ((H' * (V' * T'⁻¹) * H'⁻¹ * (V' * T'⁻¹)⁻¹).val - 1) ≤ 9 / 1000 := by
    linarith
  have hword : hsNorm ((finiteNoDriftFrameUnitary F hF
      (H * (V * (U j)⁻¹) * H⁻¹ * (V * (U j)⁻¹)⁻¹)).val - 1) ≤ 9 / 1000 := by
    simpa only [finiteNoDriftFrameUnitary_word] using hwsmall
  have hscale : Real.sqrt ((n : ℝ) / d) ≤ 2 :=
    finiteNoDrift_dimension_factor (by positivity) hηsmall hdim
  have hfinal := finiteNoDriftFrameUnitary_recover F hF hscale _ hword
  linarith

end ThomGame.Analysis
