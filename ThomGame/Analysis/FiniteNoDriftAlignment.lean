module

public import ThomGame.Analysis.FiniteNoDriftPerturbation

/-! Transport forward near inclusion when both an algebra and its unitary tuple are corrected. -/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d]

set_option maxHeartbeats 1000000

theorem finiteNoDrift_conjugation_contract (U : UnitaryMatrix d) (X : CMatrix d)
    (hX : matrixOpNorm X ≤ 1) : matrixOpNorm (U.valᴴ * X * U.val) ≤ 1 := by
  have hi : matrixOpNorm U.valᴴ ≤ 1 := matrixOpNorm_unitary_le U⁻¹
  calc
    _ ≤ matrixOpNorm (U.valᴴ * X) * matrixOpNorm U.val := matrixOpNorm_mul_le _ _
    _ ≤ (matrixOpNorm U.valᴴ * matrixOpNorm X) * matrixOpNorm U.val := by
      exact mul_le_mul_of_nonneg_right (matrixOpNorm_mul_le _ _) (matrixOpNorm_nonneg _)
    _ ≤ (1 * 1) * 1 :=
      mul_le_mul (mul_le_mul hi hX (matrixOpNorm_nonneg _) (by norm_num))
        (matrixOpNorm_unitary_le U) (matrixOpNorm_nonneg _) (by norm_num)
    _ = 1 := by ring

theorem finiteNoDrift_conjugation_norm (U : UnitaryMatrix d) (X : CMatrix d) :
    hsNorm (U.valᴴ * X * U.val) = hsNorm X := by
  rw [hsNorm_mul_unitary]
  exact hsNorm_unitary_mul U⁻¹ X

theorem finiteNoDrift_conjugation_lipschitz (U V : UnitaryMatrix d)
    (X : CMatrix d) (hX : matrixOpNorm X ≤ 1) :
    hsNorm (U.valᴴ * X * U.val - V.valᴴ * X * V.val) ≤ 2 * hsNorm (U.val - V.val) := by
  have he : U.valᴴ * X * U.val - V.valᴴ * X * V.val =
      (U.valᴴ - V.valᴴ) * X * U.val + V.valᴴ * (X * (U.val - V.val)) := by noncomm_ring
  have ht := hsNorm_add_le ((U.valᴴ - V.valᴴ) * X * U.val) (V.valᴴ * (X * (U.val - V.val)))
  have hv : hsNorm (V.valᴴ * (X * (U.val - V.val))) = hsNorm (X * (U.val - V.val)) :=
    hsNorm_unitary_mul V⁻¹ _
  rw [← he, hsNorm_mul_unitary, hv] at ht
  have hleft := hsNorm_mul_le_right (U.valᴴ - V.valᴴ) X
  rw [← Matrix.conjTranspose_sub, hsNorm_conjTranspose] at hleft
  rw [Matrix.conjTranspose_sub] at hleft
  have hright := hsNorm_mul_le_left X (U.val - V.val)
  have hl := mul_le_mul_of_nonneg_left hX (hsNorm_nonneg (U.val - V.val))
  have hr := mul_le_mul_of_nonneg_right hX (hsNorm_nonneg (U.val - V.val))
  nlinarith

theorem finiteNoDrift_forward_transfer
    (A₀ A : StarSubalgebra ℂ (CMatrix d)) (U V : UnitaryMatrix d)
    {rA ζ η : ℝ} (hA : MatrixNearInclusion A A₀ rA)
    (hA₀ : MatrixNearInclusion A₀ A rA) (hUV : hsNorm (U.val - V.val) ≤ ζ)
    (hforward : MatrixNearInclusion (matrixUnitaryPullbackAlgebra A₀ U) A₀ η) :
    MatrixNearInclusion (matrixUnitaryPullbackAlgebra A V) A (η + 2 * rA + 2 * ζ) := by
  intro X hXA hX
  let Y := (matrixUnitaryPullbackEquiv A V ⟨X, hXA⟩ : CMatrix d)
  have hYA : Y ∈ A := (matrixUnitaryPullbackEquiv A V ⟨X, hXA⟩).property
  have hYn : matrixOpNorm Y ≤ 1 := by
    have hn := finiteNoDrift_conjugation_contract V⁻¹ X hX
    change matrixOpNorm (V.valᴴᴴ * X * V.valᴴ) ≤ 1 at hn
    dsimp only [Y]
    rw [matrixUnitaryPullbackEquiv_coe]
    simpa only [Matrix.conjTranspose_conjTranspose] using hn
  obtain ⟨Y₀, hY₀, hY₀n, hYY₀⟩ := matrixNearInclusion_contraction A A₀ hA Y hYA hYn
  have hP : U.valᴴ * Y₀ * U.val ∈ matrixUnitaryPullbackAlgebra A₀ U := ⟨Y₀, hY₀, rfl⟩
  obtain ⟨Z₀, hZ₀, hZ₀n, hZ₀dist⟩ := matrixNearInclusion_contraction _ _ hforward _ hP
    (finiteNoDrift_conjugation_contract U Y₀ hY₀n)
  obtain ⟨Z, hZA, hZZ⟩ := hA₀ Z₀ hZ₀ hZ₀n
  have hunit : V.valᴴ * V.val = 1 := V.prop.1
  have hYX : V.valᴴ * Y * V.val = X := by
    dsimp only [Y]
    rw [matrixUnitaryPullbackEquiv_coe]
    calc
      _ = (V.valᴴ * V.val) * X * (V.valᴴ * V.val) := by simp only [mul_assoc]
      _ = X := by rw [hunit, one_mul, mul_one]
  have h₁ : hsNorm (X - V.valᴴ * Y₀ * V.val) ≤ rA := by
    rw [← hYX, ← sub_mul, ← mul_sub, finiteNoDrift_conjugation_norm]
    exact hYY₀
  have h₂ := finiteNoDrift_conjugation_lipschitz V U Y₀ hY₀n
  rw [hsNorm_sub_comm V.val U.val] at h₂
  have ht := rectHSNorm_sub_triangle_three d X (V.valᴴ * Y₀ * V.val) (U.valᴴ * Y₀ * U.val) Z₀
  have ht' := rectHSNorm_sub_triangle d X Z₀ Z
  refine ⟨Z, hZA, ?_⟩
  change hsNorm _ ≤ hsNorm _ + hsNorm _ + hsNorm _ at ht
  change hsNorm _ ≤ hsNorm _ + hsNorm _ at ht'
  linarith

theorem finiteNoDrift_alignment_tuple
    (A₀ D₀ A D : StarSubalgebra ℂ (CMatrix d)) {h : Nat}
    (U : Fin h → UnitaryMatrix d) {rA rD ρ η K ν : ℝ}
    (hA : MatrixNearInclusion A A₀ rA) (hA₀ : MatrixNearInclusion A₀ A rA)
    (hD : MatrixNearInclusion D D₀ rD) (hD₀ : MatrixNearInclusion D₀ D rD)
    (hcomm : ∀ j X, X ∈ D₀ → matrixOpNorm X ≤ 1 →
      hsNorm (X * (U j).val - (U j).val * X) ≤ ρ)
    (hforward : ∀ j, MatrixNearInclusion (matrixUnitaryPullbackAlgebra A₀ (U j)) A₀ η)
    (hK : 0 ≤ K) (hanchor : FiniteNoDriftAnchor A₀ D₀ U K ν) :
    ∃ V : Fin h → UnitaryMatrix d,
      (∀ j X, X ∈ D → (V j).val * X = X * (V j).val) ∧
      (∀ j, hsNorm ((U j).val - (V j).val) ≤ 3 * (ρ + 2 * rD)) ∧
      (∀ j, MatrixNearInclusion (matrixUnitaryPullbackAlgebra A (V j)) A
        (η + 2 * rA + 2 * (3 * (ρ + 2 * rD)))) ∧
      FiniteNoDriftAnchor A D V K (ν + rA + rD + 2 * K * (rA + 3 * (ρ + 2 * rD))) := by
  choose V hVD hUV using fun j => finiteNoDrift_unitary_correction D (U j)
    (finiteNoDrift_near_commutator_bound D₀ D (U j) hD (hcomm j))
  exact ⟨V, hVD, hUV,
    fun j => finiteNoDrift_forward_transfer A₀ A (U j) (V j) hA hA₀ (hUV j) (hforward j),
    finiteNoDrift_anchor_transfer A₀ D₀ A D U V hA hD₀ hUV hK hanchor⟩

end ThomGame.Analysis
