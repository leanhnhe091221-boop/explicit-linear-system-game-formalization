module

public import ThomGame.Analysis.FiniteNoDriftFrame

/-! Alignment of a near inclusion in one finite enlargement, with all error terms explicit. -/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d]

theorem finiteNoDrift_near_mono {A B : StarSubalgebra ℂ (CMatrix d)} {r s : ℝ}
    (hAB : MatrixNearInclusion A B r) (hrs : r ≤ s) : MatrixNearInclusion A B s := by
  intro X hXA hXn
  obtain ⟨Y, hYB, he⟩ := hAB X hXA hXn
  exact ⟨Y, hYB, he.trans hrs⟩

/-- A single finite stabilization makes the inclusion and commutation exact.
The original Poincare coefficient `K` is preserved. -/
theorem finiteNoDrift_stabilize
    (A₀ D₀ : StarSubalgebra ℂ (CMatrix d)) {h : Nat} (U : Fin h → UnitaryMatrix d)
    {η₀ ρ η K ν : ℝ} (hη₀ : 0 ≤ η₀) (hK : 0 ≤ K) (hν : 0 ≤ ν)
    (hDA : MatrixNearInclusion D₀ A₀ η₀)
    (hcomm : ∀ j X, X ∈ D₀ → matrixOpNorm X ≤ 1 → hsNorm (X * (U j).val - (U j).val * X) ≤ ρ)
    (hforward : ∀ j, MatrixNearInclusion (matrixUnitaryPullbackAlgebra A₀ (U j)) A₀ η)
    (hanchor : FiniteNoDriftAnchor A₀ D₀ U K ν) :
    ∃ n : Nat, ∃ hn : NeZero n, ∃ F : Matrix (Fin n) (Fin d) ℂ, ∃ hF : Fᴴ * F = 1,
    ∃ A D : StarSubalgebra ℂ (CMatrix n), ∃ V : Fin h → UnitaryMatrix n,
      d ≤ n ∧ |(n : ℝ) / d - 1| ≤ 4 * η₀ ^ 2 ∧ D ≤ A ∧
      MatrixNearInclusion A (matrixFrameScalarAlgebra A₀ F hF) (4 * η₀) ∧
      MatrixNearInclusion (matrixFrameScalarAlgebra A₀ F hF) A (4 * η₀) ∧
      MatrixNearInclusion D (matrixFrameScalarAlgebra D₀ F hF) (16 * η₀) ∧
      MatrixNearInclusion (matrixFrameScalarAlgebra D₀ F hF) D (16 * η₀) ∧
      (∀ j X, X ∈ D → (V j).val * X = X * (V j).val) ∧
      (∀ j, hsNorm ((finiteNoDriftFrameUnitary F hF (U j)).val - (V j).val) ≤ 3 * ρ + 96 * η₀) ∧
      (∀ j, MatrixNearInclusion (matrixUnitaryPullbackAlgebra A (V j)) A (η + 200 * η₀ + 6 * ρ)) ∧
      FiniteNoDriftAnchor A D V K (ν + 20 * η₀ + 2 * K * (100 * η₀ + 3 * ρ)) := by
  obtain ⟨S⟩ := exists_matrixThomSpectralData A₀ D₀ ⊥ bot_le bot_le hη₀ hDA
  letI hn : NeZero S.stableDim := ⟨Nat.ne_of_gt (lt_of_lt_of_le (NeZero.pos d) S.le_stableDim)⟩
  let F := S.stableSourceFrame
  let hF := S.stableSourceFrame_initial
  let A := S.stableCorrectedAlgebra S.correctedTargetAlgebra
  let D := S.stableCorrectedAlgebra S.correctedSourceAlgebra
  let U' := fun j => finiteNoDriftFrameUnitary F hF (U j)
  have hs3 : Real.sqrt (3 : ℝ) ≤ 2 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  have hs2 : Real.sqrt (2 : ℝ) ≤ 2 := finiteNoDrift_sqrt_two_le_two
  have ha : 2 * Real.sqrt 3 * η₀ ≤ 4 * η₀ := by nlinarith
  have hd : (6 + 5 * Real.sqrt 2) * η₀ ≤ 16 * η₀ := by nlinarith
  have hA : MatrixNearInclusion A (S.stableOriginalAlgebra A₀) (4 * η₀) :=
    finiteNoDrift_near_mono (S.stable_A_nearInclusions hη₀).2 ha
  have hA₀ : MatrixNearInclusion (S.stableOriginalAlgebra A₀) A (4 * η₀) :=
    finiteNoDrift_near_mono (S.stable_A_nearInclusions hη₀).1 ha
  have hD : MatrixNearInclusion D (S.stableOriginalAlgebra D₀) (16 * η₀) :=
    finiteNoDrift_near_mono (S.stable_B_nearInclusions hη₀ hDA).2 hd
  have hD₀ : MatrixNearInclusion (S.stableOriginalAlgebra D₀) D (16 * η₀) :=
    finiteNoDrift_near_mono (S.stable_B_nearInclusions hη₀ hDA).1 hd
  have hc : ∀ j X, X ∈ S.stableOriginalAlgebra D₀ → matrixOpNorm X ≤ 1 →
      hsNorm (X * (U' j).val - (U' j).val * X) ≤ ρ :=
    fun j => finiteNoDriftFrame_commutator_bound F hF S.le_stableDim D₀ (U j) (hcomm j)
  have hf : ∀ j, MatrixNearInclusion (matrixUnitaryPullbackAlgebra (S.stableOriginalAlgebra A₀) (U' j))
      (S.stableOriginalAlgebra A₀) η :=
    fun j => finiteNoDriftFrame_forward F hF S.le_stableDim A₀ (U j) (hforward j)
  have hh : FiniteNoDriftAnchor (S.stableOriginalAlgebra A₀) (S.stableOriginalAlgebra D₀) U' K ν :=
    finiteNoDriftFrame_anchor F hF S.le_stableDim A₀ D₀ U hν hanchor
  obtain ⟨V, hv, he, hf', hh'⟩ := finiteNoDrift_alignment_tuple
    (S.stableOriginalAlgebra A₀) (S.stableOriginalAlgebra D₀) A D U' hA hA₀ hD hD₀ hc hf hK hh
  refine ⟨S.stableDim, hn, F, hF, A, D, V, S.le_stableDim, S.stableDim_ratio_bound,
    S.stableCorrected_inclusion, hA, hA₀, hD, hD₀, hv, ?_, ?_, ?_⟩
  · intro j
    convert he j using 1 <;> ring
  · intro j
    convert hf' j using 1 <;> ring
  · convert hh' using 1 <;> ring

end ThomGame.Analysis
