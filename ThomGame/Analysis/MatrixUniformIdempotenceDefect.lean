module

public import ThomGame.Analysis.UniformMatrixNormTransfer
public import ThomGame.Analysis.MatrixRelativeExpectation

/-!
# Vanishing coordinate idempotence defect of an induced expectation

The first quantitative input of ALT reconstruction follows from the
actual quotient map: idempotence is equivalent to vanishing coordinate
operator-to-Hilbert--Schmidt defect. No rate is assumed.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

namespace UniformMatrixMap

variable {dims : Nat → Nat} (F : UniformMatrixMap dims)
  (hd : ∀ k, 0 < dims k) (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop)

include hL in
theorem quotientMap_idempotent_iff_defect_tendsto_zero :
    (∀ x, F.quotientMap (L : Filter Nat) (F.quotientMap (L : Filter Nat) x) =
      F.quotientMap (L : Filter Nat) x) ↔
    Tendsto (((F.comp F).sub F).coordinateMixedNorm hd) (L : Filter Nat) (𝓝 0) := by
  rw [← (F.comp F).quotientMap_eq_iff_mixedNorm_sub_tendsto_zero hd L hL F]
  constructor
  · intro h
    apply LinearMap.ext
    intro x
    rw [comp_quotientMap]
    exact h x
  · intro h x
    have he := congrArg (fun P : MatrixTracialQuotient dims (L : Filter Nat) →ₗ[ℂ]
      MatrixTracialQuotient dims (L : Filter Nat) => P x) h
    simpa only [comp_quotientMap] using he

theorem idempotenceDefect_hsNorm_le (k : Nat) (X : CMatrix (dims k)) :
    hsNorm (F.toLinearMap k (F.toLinearMap k X) - F.toLinearMap k X) ≤
      ((F.comp F).sub F).coordinateMixedNorm hd k * matrixOpNorm X :=
  ((F.comp F).sub F).hsNorm_apply_le_coordinateMixedNorm hd k X

end UniformMatrixMap

theorem matrixUniformMap_idempotenceDefect_tendsto_zero (dims : Nat → Nat) {h : Nat} [NeZero h]
    (U : (k : Nat) → Fin h → UnitaryMatrix (dims k)) (hd : ∀ k, 0 < dims k)
    (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop) (F : UniformMatrixMap dims)
    (hF : F.quotientMap (L : Filter Nat) = matrixRelativeExpectation dims U hd L hL) :
    Tendsto (((F.comp F).sub F).coordinateMixedNorm hd) (L : Filter Nat) (𝓝 0) := by
  apply (F.quotientMap_idempotent_iff_defect_tendsto_zero hd L hL).mp
  intro x
  rw [hF, matrixRelativeExpectation_idem]

end ThomGame.Analysis
