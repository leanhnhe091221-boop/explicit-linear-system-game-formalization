module

public import ThomGame.Analysis.MatrixDimensionCutTarget

/-!
# Uniform unit-ball estimates in the standard target corner

Both directions use actual contractions. The only errors are the lost
support trace and conjugation by the near-identity unitary.
-/

@[expose] public section
namespace ThomGame.Analysis.MatrixDimensionCutTarget

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {m d : Nat} {A : StarSubalgebra ℂ (CMatrix m)}
    {S : MatrixSubalgebraDimensionCut A d} {hd : d ≤ m} (T : MatrixDimensionCutTarget S hd)

theorem forward_approximation (r : Nat) (X : CMatrix m) (hX : X ∈ A) (hn : matrixOpNorm X ≤ 1) :
    ∃ Y ∈ T.liftedAlgebra, matrixOpNorm Y ≤ 1 ∧
      rectHSNorm r (X - Y) ≤ Real.sqrt (2 * matrixTraceReal r (1 - S.frame * S.frameᴴ)) +
        2 * rectHSNorm r (T.unitary.val - 1) := by
  let C := S.frameᴴ * X * S.frame
  let Z := matrixFrameLift S.frame C
  let Y := matrixFrameLift T.fullFrame C
  have hCn : matrixOpNorm C ≤ 1 := (matrixFrameCompression_opNorm_le S.frame S.initial X).trans hn
  have hZn : matrixOpNorm Z ≤ 1 := by rwa [matrixFrameLift_opNorm S.frame S.initial]
  have hYn : matrixOpNorm Y ≤ 1 := by rwa [matrixFrameLift_opNorm T.fullFrame T.fullFrame_initial]
  refine ⟨Y, T.fullFrame_lift_mem C (S.compression_mem X hX), hYn, ?_⟩
  have h₁ : rectHSNorm r (X - Z) ≤ Real.sqrt (2 * matrixTraceReal r (1 - S.frame * S.frameᴴ)) :=
    matrixDimensionCut_compression_loss S r X hn
  have h₂ : rectHSNorm r (Z - Y) ≤ 2 * rectHSNorm r (T.unitary.val - 1) := by
    dsimp only [Y]
    rw [T.fullFrame_lift]
    exact matrixUnitary_conjugation_distance r T.unitary Z hZn
  exact (rectHSNorm_sub_triangle r X Z Y).trans (add_le_add h₁ h₂)

theorem reverse_approximation (r : Nat) (Y : CMatrix m) (hY : Y ∈ T.liftedAlgebra)
    (hn : matrixOpNorm Y ≤ 1) :
    ∃ X ∈ A, matrixOpNorm X ≤ 1 ∧
      rectHSNorm r (Y - X) ≤ 2 * Real.sqrt (2 * matrixTraceReal r (1 - S.frame * S.frameᴴ)) +
        2 * rectHSNorm r (T.unitary.val - 1) := by
  let C := T.fullFrameᴴ * Y * T.fullFrame
  have hC : C ∈ S.algebra := T.fullFrame_compression_mem Y hY
  have hCn : matrixOpNorm C ≤ 1 :=
    (matrixFrameCompression_opNorm_le T.fullFrame T.fullFrame_initial Y).trans hn
  obtain ⟨X, hX, hnX, he⟩ := S.contraction_lift C hC hCn
  let Z := matrixFrameLift S.frame C
  let W := matrixFrameLift T.fullFrame C
  have hZn : matrixOpNorm Z ≤ 1 := by rwa [matrixFrameLift_opNorm S.frame S.initial]
  have h₁ : rectHSNorm r (Y - W) ≤ Real.sqrt (2 * matrixTraceReal r (1 - S.frame * S.frameᴴ)) :=
    T.fullFrame_compression_loss r Y hn
  have h₂ : rectHSNorm r (W - Z) ≤ 2 * rectHSNorm r (T.unitary.val - 1) := by
    rw [rectHSNorm_sub_comm]
    dsimp only [W]
    rw [T.fullFrame_lift]
    exact matrixUnitary_conjugation_distance r T.unitary Z hZn
  have h₃ : rectHSNorm r (Z - X) ≤ Real.sqrt (2 * matrixTraceReal r (1 - S.frame * S.frameᴴ)) := by
    rw [rectHSNorm_sub_comm]
    have h := matrixDimensionCut_compression_loss S r X hnX
    rwa [he] at h
  refine ⟨X, hX, hnX, ?_⟩
  have ht := (rectHSNorm_sub_triangle_three r Y W Z X).trans (add_le_add (add_le_add h₁ h₂) h₃)
  linarith only [ht]

theorem unitBall_approximations :
    (∀ X ∈ A, matrixOpNorm X ≤ 1 → ∃ Y ∈ T.liftedAlgebra, matrixOpNorm Y ≤ 1 ∧
      rectHSNorm m (X - Y) ≤ 2 * Real.sqrt (2 * matrixTraceReal m (1 - S.frame * S.frameᴴ)) +
        8 * Real.sqrt (matrixTraceReal m (1 - S.frame * S.frameᴴ))) ∧
    (∀ Y ∈ T.liftedAlgebra, matrixOpNorm Y ≤ 1 → ∃ X ∈ A, matrixOpNorm X ≤ 1 ∧
      rectHSNorm m (Y - X) ≤ 2 * Real.sqrt (2 * matrixTraceReal m (1 - S.frame * S.frameᴴ)) +
        8 * Real.sqrt (matrixTraceReal m (1 - S.frame * S.frameᴴ))) := by
  constructor
  · intro X hX hn
    obtain ⟨Y, hY, hYn, he⟩ := T.forward_approximation m X hX hn
    refine ⟨Y, hY, hYn, ?_⟩
    linarith only [he, T.near, Real.sqrt_nonneg (2 * matrixTraceReal m (1 - S.frame * S.frameᴴ))]
  · intro Y hY hn
    obtain ⟨X, hX, hXn, he⟩ := T.reverse_approximation m Y hY hn
    exact ⟨X, hX, hXn, by linarith only [he, T.near]⟩

theorem hausdorff_bound [NeZero m] :
    matrixHSUnitBallHausdorff m A T.liftedAlgebra ≤
      2 * Real.sqrt (2 * matrixTraceReal m (1 - S.frame * S.frameᴴ)) +
        8 * Real.sqrt (matrixTraceReal m (1 - S.frame * S.frameᴴ)) :=
  matrixHSUnitBallHausdorff_le m A T.liftedAlgebra (by positivity)
    T.unitBall_approximations.1 T.unitBall_approximations.2

end ThomGame.Analysis.MatrixDimensionCutTarget
