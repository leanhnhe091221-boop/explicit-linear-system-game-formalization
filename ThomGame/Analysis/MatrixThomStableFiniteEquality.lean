module

public import ThomGame.Analysis.MatrixThomStableInternalEquality

/-!
# The stable equalities in the actual finite weakly closed model

The faithful representation carries each equality of internal tracial
quotient algebras to equality in the associated finite operator algebra.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

theorem matrixInternalFiniteAlgebra_eq_of_quotient_eq (dims : Nat → Nat)
    (A B : (n : Nat) → StarSubalgebra ℂ (CMatrix (dims n))) (hd : ∀ n, 0 < dims n)
    (L : Ultrafilter Nat)
    (h : matrixInternalQuotient dims A (L : Filter Nat) = matrixInternalQuotient dims B (L : Filter Nat)) :
    matrixInternalFiniteAlgebra dims A hd L = matrixInternalFiniteAlgebra dims B hd L :=
  le_antisymm ((matrixInternalFiniteAlgebra_le_iff dims A B hd L).mpr h.le)
    ((matrixInternalFiniteAlgebra_le_iff dims B A hd L).mpr h.ge)

variable (dims : Nat → Nat) [∀ n, NeZero (dims n)]
    {A B D : (n : Nat) → StarSubalgebra ℂ (CMatrix (dims n))} {ε : Nat → ℝ}
    (S : (n : Nat) → MatrixThomSpectralData (A n) (B n) (D n) (ε n)) (L : Ultrafilter Nat)

theorem matrixThom_stable_A_finite_eq (hε : Tendsto ε (L : Filter Nat) (𝓝 0))
    (hε0 : ∀ n, 0 ≤ ε n) :
    matrixInternalFiniteAlgebra (fun n => (S n).stableDim) (fun n => (S n).stableOriginalAlgebra (A n))
        (fun n => (NeZero.pos (dims n)).trans_le (S n).le_stableDim) L =
      matrixInternalFiniteAlgebra (fun n => (S n).stableDim)
        (fun n => (S n).stableCorrectedAlgebra (S n).correctedTargetAlgebra)
        (fun n => (NeZero.pos (dims n)).trans_le (S n).le_stableDim) L :=
  matrixInternalFiniteAlgebra_eq_of_quotient_eq _ _ _ _ L
    (matrixThom_stable_A_internal_eq dims S hε hε0)

theorem matrixThom_stable_B_finite_eq (hε : Tendsto ε (L : Filter Nat) (𝓝 0))
    (hε0 : ∀ n, 0 ≤ ε n) (hBA : ∀ n, MatrixNearInclusion (B n) (A n) (ε n)) :
    matrixInternalFiniteAlgebra (fun n => (S n).stableDim) (fun n => (S n).stableOriginalAlgebra (B n))
        (fun n => (NeZero.pos (dims n)).trans_le (S n).le_stableDim) L =
      matrixInternalFiniteAlgebra (fun n => (S n).stableDim)
        (fun n => (S n).stableCorrectedAlgebra (S n).correctedSourceAlgebra)
        (fun n => (NeZero.pos (dims n)).trans_le (S n).le_stableDim) L :=
  matrixInternalFiniteAlgebra_eq_of_quotient_eq _ _ _ _ L
    (matrixThom_stable_B_internal_eq dims S hε hε0 hBA)

end ThomGame.Analysis
