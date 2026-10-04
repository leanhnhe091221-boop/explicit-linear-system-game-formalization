module

public import ThomGame.Analysis.MatrixThomStableNearInclusion
public import ThomGame.Analysis.MatrixFiniteNearInclusion

/-!
# Equality of the corrected internal algebras in the stable tracial quotient

Both directions follow from genuine coordinate near inclusions. The
quotient uses the enlarged ambient dimension N, whose relation to the
original-denominator estimates was proved explicitly.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

theorem matrixInternal_eq_of_mutual_nearInclusion_errors {ι : Type*}
    (dims : ι → Nat) [∀ n, NeZero (dims n)]
    (A B : (n : ι) → StarSubalgebra ℂ (CMatrix (dims n))) (L : Filter ι)
    (δ : ι → ℝ) (hδ : Tendsto δ L (𝓝 0))
    (hAB : ∀ n, MatrixNearInclusion (A n) (B n) (δ n))
    (hBA : ∀ n, MatrixNearInclusion (B n) (A n) (δ n)) :
    matrixInternalQuotient dims A L = matrixInternalQuotient dims B L :=
  le_antisymm (matrixInternal_le_of_nearInclusion_errors dims A B
    (fun n => NeZero.pos (dims n)) L δ hδ hAB)
    (matrixInternal_le_of_nearInclusion_errors dims B A
      (fun n => NeZero.pos (dims n)) L δ hδ hBA)

variable {ι : Type*} (dims : ι → Nat) [∀ n, NeZero (dims n)]
    {A B D : (n : ι) → StarSubalgebra ℂ (CMatrix (dims n))} {ε : ι → ℝ}
    (S : (n : ι) → MatrixThomSpectralData (A n) (B n) (D n) (ε n)) {L : Filter ι}

theorem matrixThom_stable_A_internal_eq (hε : Tendsto ε L (𝓝 0)) (hε0 : ∀ n, 0 ≤ ε n) :
    matrixInternalQuotient (fun n => (S n).stableDim) (fun n => (S n).stableOriginalAlgebra (A n)) L =
      matrixInternalQuotient (fun n => (S n).stableDim)
        (fun n => (S n).stableCorrectedAlgebra (S n).correctedTargetAlgebra) L := by
  let : ∀ n, NeZero (S n).stableDim :=
    fun n => ⟨Nat.ne_of_gt ((NeZero.pos (dims n)).trans_le (S n).le_stableDim)⟩
  exact matrixInternal_eq_of_mutual_nearInclusion_errors _ _ _ L
    (fun n => 2 * Real.sqrt 3 * ε n) (by simpa using hε.const_mul (2 * Real.sqrt 3))
    (fun n => ((S n).stable_A_nearInclusions (hε0 n)).1)
    (fun n => ((S n).stable_A_nearInclusions (hε0 n)).2)

theorem matrixThom_stable_B_internal_eq (hε : Tendsto ε L (𝓝 0)) (hε0 : ∀ n, 0 ≤ ε n)
    (hBA : ∀ n, MatrixNearInclusion (B n) (A n) (ε n)) :
    matrixInternalQuotient (fun n => (S n).stableDim) (fun n => (S n).stableOriginalAlgebra (B n)) L =
      matrixInternalQuotient (fun n => (S n).stableDim)
        (fun n => (S n).stableCorrectedAlgebra (S n).correctedSourceAlgebra) L := by
  let : ∀ n, NeZero (S n).stableDim :=
    fun n => ⟨Nat.ne_of_gt ((NeZero.pos (dims n)).trans_le (S n).le_stableDim)⟩
  exact matrixInternal_eq_of_mutual_nearInclusion_errors _ _ _ L
    (fun n => (6 + 5 * Real.sqrt 2) * ε n) (by simpa using hε.const_mul (6 + 5 * Real.sqrt 2))
    (fun n => ((S n).stable_B_nearInclusions (hε0 n) (hBA n)).1)
    (fun n => ((S n).stable_B_nearInclusions (hε0 n) (hBA n)).2)

end ThomGame.Analysis
