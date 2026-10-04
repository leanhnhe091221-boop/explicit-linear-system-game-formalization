module

public import ThomGame.Analysis.MatrixALTExpectationConvergence
public import ThomGame.Analysis.MatrixALTCorollary5_1
public import ThomGame.Analysis.MatrixUniformIdempotenceDefect
public import ThomGame.Analysis.UniformMatrixExpectations

/-!
# Internal relative commutants from the actual ALT reconstruction

The spectral gap remains a hypothesis about the actual ultraproduct.
Corollary 5.1 constructs its lifts; finite reconstruction constructs the
coordinate algebras, and equality of expectations identifies their image.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra

theorem matrixMixedNorm_approximation_induces_expectation (dims : Nat → Nat)
    [∀ n, NeZero (dims n)] (F : UniformMatrixMap dims)
    (A : (n : Nat) → StarSubalgebra ℂ (CMatrix (dims n))) (hd : ∀ n, 0 < dims n)
    (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop)
    (happrox : Tendsto (fun n => matrixMixedNorm (F.toLinearMap n - matrixTraceProjection (A n)))
      (L : Filter Nat) (𝓝 0)) :
    F.quotientMap (L : Filter Nat) = matrixQuotientExpectation dims A hd (L : Filter Nat) :=
  (quotientMap_eq_expectation_iff_mixedNorm_tendsto_zero dims A hd L hL F).mpr happrox

theorem exists_matrixALT_internal_relative_commutant (dims : Nat → Nat) {h : Nat} [NeZero h]
    (U : (k : Nat) → Fin h → UnitaryMatrix (dims k)) (hd : ∀ k, 0 < dims k)
    (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop) (κ : ℝ)
    (hgap : MatrixMarkovSpectralGap dims U hd L κ) :
    ∃ A : (k : Nat) → StarSubalgebra ℂ (CMatrix (dims k)),
      matrixRelativeExpectation dims U hd L hL = matrixQuotientExpectation dims A hd (L : Filter Nat) ∧
      matrixRelativeCommutant dims U (L : Filter Nat) = matrixInternalQuotient dims A (L : Filter Nat) := by
  let (k : Nat) : NeZero (dims k) := ⟨Nat.ne_of_gt (hd k)⟩
  obtain ⟨T, Q, N, Ψ, hne, _, _, _, _, _, hΨ, h1, htrace, hbimod, hpair, hexpect, hsigma, _, _⟩ :=
    exists_matrixUltraproduct_ALT_corollary5_1 dims U hd L hL κ hgap
  let F := matrixUniformMarkovPower dims T hd N
  have hdelta : Tendsto (fun k => matrixMixedNorm ((Ψ k).toLinearMap.comp (Ψ k).toLinearMap - (Ψ k).toLinearMap))
      (L : Filter Nat) (𝓝 0) := by
    have hdelt := matrixUniformMap_idempotenceDefect_tendsto_zero dims U hd L hL F hexpect
    change Tendsto (fun k => matrixMixedNorm ((F.toLinearMap k).comp (F.toLinearMap k) - F.toLinearMap k))
      (L : Filter Nat) (𝓝 0) at hdelt
    simpa only [hΨ] using hdelt
  have hmix : Tendsto (fun k => matrixScalarMixingError (Q k).E (Ψ k).toLinearMap)
      (L : Filter Nat) (𝓝 0) := by
    have he : (fun k => matrixScalarMixingError (Q k).E (Ψ k).toLinearMap) =
        matrixScalarCornerErrorSequence dims T hd Q N := by
      funext k
      rw [hΨ k]
      exact matrixScalarMixingError_markov (Q k) (N k)
    rw [he]
    exact hsigma
  obtain ⟨A, _, happrox⟩ := exists_matrixALT_expectation_approximation dims (fun k => Fin (Q k).n)
    Ψ h1 htrace hpair (fun k => (Q k).E) (fun k => (Q k).projection) hne
    (fun k => (Q k).orthogonal) (fun k => (Q k).sum_one) hbimod (L : Filter Nat) hL hdelta hmix
  have he : F.quotientMap (L : Filter Nat) = matrixQuotientExpectation dims A hd (L : Filter Nat) :=
    matrixMixedNorm_approximation_induces_expectation dims F A hd L hL (by simpa only [hΨ] using happrox)
  have he' : matrixRelativeExpectation dims U hd L hL = matrixQuotientExpectation dims A hd (L : Filter Nat) :=
    hexpect.symm.trans he
  refine ⟨A, he', ?_⟩
  have hr := congrArg LinearMap.range he'
  rw [matrixRelativeExpectation_range, matrixQuotientExpectation_range] at hr
  ext x
  exact SetLike.ext_iff.mp hr x

end ThomGame.Analysis
