module

public import ThomGame.Analysis.MatrixALTPrunedDecomposition
public import ThomGame.Analysis.MatrixUltraproductALTOrthogonalSelection

/-!
# Pruned ALT decompositions under the genuine ultraproduct spectral gap

The coordinates on an ultrafilter-large set have actual finite
partitions, doubled reducing unitary tuples and the retained scalar
gap. Both the bad-block trace bound and the edit bound tend to zero.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

theorem altBlockErrorBound_tendsto_zero {ι : Type*} {l : Filter ι} {η : ι → ℝ}
    (κ : ℝ) (hη : Tendsto η l (𝓝 0)) :
    Tendsto (fun i => altBlockErrorBound κ (η i)) l (𝓝 0) := by
  simpa only [altBlockErrorBound, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] using
    ((hη.pow 2).const_mul 85248).add (hη.const_mul (6 * (512 / κ) ^ 2))

theorem altPrunedTraceBound_tendsto_zero {ι : Type*} {l : Filter ι} {η : ι → ℝ}
    (κ : ℝ) (hη : Tendsto η l (𝓝 0)) :
    Tendsto (fun i => altPrunedTraceBound κ (η i)) l (𝓝 0) := by
  simpa only [altPrunedTraceBound, mul_zero, zero_div, add_zero] using
    (hη.const_mul 16).add (((altBlockErrorBound_tendsto_zero κ hη).const_mul 16384).div_const κ)

theorem altPrunedEditBound_tendsto_zero {ι : Type*} {l : Filter ι} {η : ι → ℝ}
    (κ : ℝ) (hη : Tendsto η l (𝓝 0)) :
    Tendsto (fun i => altPrunedEditBound κ (η i)) l (𝓝 0) := by
  simpa only [altPrunedEditBound, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] using
    (((altBlockErrorBound_tendsto_zero κ hη).const_mul 4).add
      ((altPrunedTraceBound_tendsto_zero κ hη).const_mul 16)).add ((hη.pow 2).const_mul 151552)

theorem exists_matrixUltraproduct_ALT_prunedDecomposition (dims : Nat → Nat) {h : Nat} [NeZero h]
    (U : (k : Nat) → Fin h → UnitaryMatrix (dims k)) (hd : ∀ k, 0 < dims k)
    (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop) (κ : ℝ)
    (hgap : MatrixMarkovSpectralGap dims U hd L κ) :
    ∃ η : Nat → ℝ, (∀ k, 0 < η k) ∧ Tendsto η (L : Filter Nat) (𝓝 0) ∧
      Tendsto (fun k => altPrunedTraceBound κ (η k)) (L : Filter Nat) (𝓝 0) ∧
      Tendsto (fun k => altPrunedEditBound κ (η k)) (L : Filter Nat) (𝓝 0) ∧
      ∀ᶠ k in (L : Filter Nat), Nonempty (MatrixALTPrunedDecomposition (U k) κ (η k)) := by
  obtain ⟨R, α, _, _, hR, hη, hsel⟩ :=
    exists_matrixUltraproduct_ALT_orthogonalSelection dims U hd L hL κ hgap
  refine ⟨fun k => altDecompositionScale (α k), fun k => altDecompositionScale_pos (α k),
    hη, altPrunedTraceBound_tendsto_zero κ hη, altPrunedEditBound_tendsto_zero κ hη, ?_⟩
  filter_upwards [hsel] with k hk
  let : NeZero (dims k) := ⟨Nat.ne_of_gt (hd k)⟩
  obtain ⟨sel⟩ := hk.2.2
  exact exists_matrixALT_prunedDecomposition (U k) sel (hR k).1 hgap.1 hgap.2.1.le

end ThomGame.Analysis
