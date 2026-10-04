module

public import ThomGame.Analysis.MatrixALTInternality

/-!
# The internal-range conclusion for arbitrary actual ALT lifts

Idempotence is assumed only for the induced map, and implies the required
coordinate defect convergence. The resulting coordinate algebras contain
the original scalar diagonals. Identification of centers is separate.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra

theorem exists_matrixALT_internal_range (dims : Nat → Nat) [∀ n, NeZero (dims n)]
    (μ : Nat → Type*) [∀ n, Fintype (μ n)] [∀ n, DecidableEq (μ n)]
    (F : UniformMatrixMap dims) (Ψ : (n : Nat) → CMatrix (dims n) →CP CMatrix (dims n))
    (hΨ : ∀ n, (Ψ n).toLinearMap = F.toLinearMap n)
    (h1 : ∀ n, Ψ n 1 = 1)
    (htrace : ∀ n X, normalizedTrace (Ψ n X) = normalizedTrace X)
    (hpair : ∀ n X Y, normalizedTrace (star (Ψ n X) * Y) = normalizedTrace (star X * Ψ n Y))
    (E : (n : Nat) → μ n → CMatrix (dims n))
    (hE : ∀ n i, IsStarProjection (E n i)) (hne : ∀ n i, E n i ≠ 0)
    (horth : ∀ n, Pairwise (fun i j => E n i * E n j = 0)) (hsum : ∀ n, ∑ i, E n i = 1)
    (hbimod : ∀ n A X B, A ∈ matrixPartitionScalarAlgebra (E n) → B ∈ matrixPartitionScalarAlgebra (E n) →
      Ψ n (A * X * B) = A * Ψ n X * B)
    (hd : ∀ n, 0 < dims n) (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop)
    (hidempotent : ∀ x, F.quotientMap (L : Filter Nat) (F.quotientMap (L : Filter Nat) x) =
      F.quotientMap (L : Filter Nat) x)
    (hsigma : Tendsto (fun n => matrixScalarMixingError (E n) (Ψ n).toLinearMap) (L : Filter Nat) (𝓝 0)) :
    ∃ A : (n : Nat) → StarSubalgebra ℂ (CMatrix (dims n)),
      (∀ n, matrixPartitionScalarAlgebra (E n) ≤ A n) ∧
      Tendsto (fun n => matrixMixedNorm (F.toLinearMap n - matrixTraceProjection (A n))) (L : Filter Nat) (𝓝 0) ∧
      F.quotientMap (L : Filter Nat) = matrixQuotientExpectation dims A hd (L : Filter Nat) ∧
      LinearMap.range (F.quotientMap (L : Filter Nat)) =
        (matrixInternalQuotient dims A (L : Filter Nat)).toSubalgebra.toSubmodule := by
  have hdelta : Tendsto (fun n => matrixMixedNorm ((Ψ n).toLinearMap.comp (Ψ n).toLinearMap - (Ψ n).toLinearMap))
      (L : Filter Nat) (𝓝 0) := by
    have hh := (F.quotientMap_idempotent_iff_defect_tendsto_zero hd L hL).mp hidempotent
    change Tendsto (fun n => matrixMixedNorm ((F.toLinearMap n).comp (F.toLinearMap n) - F.toLinearMap n))
      (L : Filter Nat) (𝓝 0) at hh
    simpa only [hΨ] using hh
  obtain ⟨A, hD, happrox⟩ := exists_matrixALT_expectation_approximation dims μ Ψ h1 htrace hpair
    E hE hne horth hsum hbimod (L : Filter Nat) hL hdelta hsigma
  have happrox' : Tendsto (fun n => matrixMixedNorm (F.toLinearMap n - matrixTraceProjection (A n)))
      (L : Filter Nat) (𝓝 0) := by simpa only [hΨ] using happrox
  have he := matrixMixedNorm_approximation_induces_expectation dims F A hd L hL happrox'
  refine ⟨A, hD, happrox', he, ?_⟩
  rw [he, matrixQuotientExpectation_range]

end ThomGame.Analysis
