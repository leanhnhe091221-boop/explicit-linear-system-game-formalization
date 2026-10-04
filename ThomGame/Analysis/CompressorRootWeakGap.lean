module

public import ThomGame.Analysis.CompressorRootAverages
public import ThomGame.Analysis.FinitePairAverageDilation
public import ThomGame.Analysis.DilationQuadraticTransfer
public import ThomGame.Analysis.FiniteThreePairCombination
public import ThomGame.Groups.PrimeFiveCoverCyclicGeneration

/-! Explicit weak root gap, obtained by regular dilation of finite class-two pairs. -/

@[expose] public noncomputable section
namespace ThomGame.Analysis

open Compressor FinitePrimeFivePair
open scoped BigOperators
variable {d r : ℕ} [NeZero d]

set_option maxHeartbeats 1600000

theorem compressorRoot_pair_bounds (f : MatrixAssignment Compressor.Generator d)
    (root : Root) (σ : Fin r → Coeff) (hr : r ≤ 7) {δ : ℝ} (hδ : 0 ≤ δ)
    (hf : IsApproxRepresentation Compressor.relators δ f) (X : CMatrix d)
    (hX : matrixOpNorm X ≤ 1) :
    let x := finiteMatrixHilbertEquiv d X
    let y := compressorRootAverage f root σ x
    let z := compressorRootAverage f (Compressor.right root) σ x
    (‖x-y‖ ^ 2 ≤ (inner ℂ x (x-y)).re + 5*(4000000000*δ)) ∧
      ((11/20:ℝ) * (inner ℂ x ((x-y)+(x-z))).re ≤
        ‖(x-y)+(x-z)‖ ^ 2 + 18*(4000000000*δ)) := by
  let : CompleteSpace (FiniteMatrixHilbert d) := FiniteDimensional.complete ℂ _
  let U := compressorPairAction f root σ
  let x := finiteMatrixHilbertEquiv d X
  let S := finiteDilation U
  let K := FiniteRegularSpace (FinitePrimeFivePair r) (FiniteMatrixHilbert d)
  let ρ : FinitePrimeFivePair r →* (K ≃ₗᵢ[ℂ] K) := finiteRegularAction
  let P : K →L[ℂ] K := pairLeftAverage ρ
  let Q : K →L[ℂ] K := pairRightAverage ρ
  have hx : ‖x‖ ≤ 1 := by
    rw [show x = finiteMatrixHilbertEquiv d X from rfl, finiteMatrixHilbert_norm]
    exact (hsNorm_le_matrixOpNorm X).trans hX
  have hη : 0 ≤ 4000000000*δ := mul_nonneg (by norm_num) hδ
  have hm (g k : FinitePrimeFivePair r) : ‖U g (U k x)-U (g*k) x‖ ≤ 4000000000*δ :=
    (compressorPairAction_mul_error f root σ hr hδ hf X hX g k).trans (by linarith)
  have hi (g k : FinitePrimeFivePair r) : ‖U g ((U k).symm x)-U (g*k⁻¹) x‖ ≤ 4000000000*δ :=
    compressorPairAction_mul_inv_error f root σ hr hδ hf X hX g k
  have hl := finitePair_left_average_intertwining U x hη hm hi
  have hr' := finitePair_right_average_intertwining U x hη hm hi
  have hleft : (fun α => U (leftVector α)) = compressorRootAction f root σ :=
    funext (compressorPairAction_left f root σ)
  have hright : (fun α => U (rightVector α)) = compressorRootAction f (Compressor.right root) σ :=
    funext (compressorPairAction_right f root σ)
  rw [hleft] at hl
  rw [hright] at hr'
  have hP : IsStarProjection P := finiteSubgroupAverage_isStarProjection ρ (leftSubgroup r)
  have hQ : IsStarProjection Q := finiteSubgroupAverage_isStarProjection ρ (rightSubgroup r)
  have hy := (compressorRootAverage_norm f root σ x).trans hx
  have hz := (compressorRootAverage_norm f (Compressor.right root) σ x).trans hx
  have hfirst := projection_residual_energy_transfer S x (compressorRootAverage f root σ x)
      P hP hη hx hy hl
  have hsecond := pair_residual_quadratic_transfer S x (compressorRootAverage f root σ x)
      (compressorRootAverage f (Compressor.right root) σ x) P Q hP hQ
      (finitePair_residual_polynomial ρ) hη hx hy hz hl hr'
  exact ⟨hfirst, hsecond⟩

theorem compressorRoot_laplacian_weak_gap (f : MatrixAssignment Compressor.Generator d)
    (σ : Fin r → Coeff) (hr : r ≤ 7) {δ : ℝ} (hδ : 0 ≤ δ)
    (hf : IsApproxRepresentation Compressor.relators δ f) (X : CMatrix d)
    (hX : matrixOpNorm X ≤ 1) :
    let x := finiteMatrixHilbertEquiv d X
    let v := fun c : Fin 3 => x - compressorRootAverage f (cyclicRoot c) σ x
    (1/10:ℝ) * (inner ℂ x (∑ c, v c)).re ≤
      ‖∑ c, v c‖ ^ 2 + 276000000000*δ := by
  dsimp only
  have hh := finiteThreePairCombination (finiteMatrixHilbertEquiv d X)
    (fun c => finiteMatrixHilbertEquiv d X -
      compressorRootAverage f (cyclicRoot c) σ (finiteMatrixHilbertEquiv d X))
    (η := 4000000000*δ)
    (fun c => by
      simpa only [PrimeFiveRankThreeCover.right_cyclicRoot, finRotate_apply] using
        (compressorRoot_pair_bounds f (cyclicRoot c) σ hr hδ hf X hX).2)
    (fun c => (compressorRoot_pair_bounds f (cyclicRoot c) σ hr hδ hf X hX).1)
  convert hh using 1 <;> ring

end ThomGame.Analysis
