module

public import ThomGame.Analysis.MatrixALTInternalRange
public import ThomGame.Analysis.MatrixInternalCenters

/-!
# ALT Theorem 5.2: coordinate algebras, expectations, internality and centers

The induced map is a projection onto the specified actual subalgebra N:
its image lies in N and it fixes N. This follows in particular when the
coordinate maps induce the conditional expectation onto N. Internality,
the coordinate algebras, their approximation, and the center equality are
conclusions, not hypotheses.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra

theorem exists_matrixALT_theorem5_2 (dims : Nat → Nat) [∀ n, NeZero (dims n)]
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
    (N : StarSubalgebra ℂ (MatrixTracialQuotient dims (L : Filter Nat)))
    (hNmem : ∀ x, F.quotientMap (L : Filter Nat) x ∈ N)
    (hNfix : ∀ x ∈ N, F.quotientMap (L : Filter Nat) x = x)
    (hsigma : Tendsto (fun n => matrixScalarMixingError (E n) (Ψ n).toLinearMap) (L : Filter Nat) (𝓝 0)) :
    ∃ A : (n : Nat) → StarSubalgebra ℂ (CMatrix (dims n)),
      (∀ n, matrixPartitionScalarAlgebra (E n) ≤ A n) ∧
      Tendsto (fun n => matrixMixedNorm (F.toLinearMap n - matrixTraceProjection (A n))) (L : Filter Nat) (𝓝 0) ∧
      F.quotientMap (L : Filter Nat) = matrixQuotientExpectation dims A hd (L : Filter Nat) ∧
      N = matrixInternalQuotient dims A (L : Filter Nat) ∧
      starSubalgebraCenter N = matrixInternalQuotient dims (fun n => starSubalgebraCenter (A n)) (L : Filter Nat) := by
  have hidem x : F.quotientMap (L : Filter Nat) (F.quotientMap (L : Filter Nat) x) =
      F.quotientMap (L : Filter Nat) x := hNfix _ (hNmem x)
  obtain ⟨A, hD, happrox, hexpect, hrange⟩ := exists_matrixALT_internal_range dims μ F Ψ hΨ h1 htrace hpair
    E hE hne horth hsum hbimod hd L hL hidem hsigma
  have hNrange : LinearMap.range (F.quotientMap (L : Filter Nat)) = N.toSubalgebra.toSubmodule := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact hNmem y
    · intro hx
      exact ⟨x, hNfix x hx⟩
  have hN : N = matrixInternalQuotient dims A (L : Filter Nat) := by
    ext x
    exact SetLike.ext_iff.mp (hNrange.symm.trans hrange) x
  refine ⟨A, hD, happrox, hexpect, hN, ?_⟩
  rw [hN, matrixInternalQuotient_center dims A hd (L : Filter Nat)]

theorem exists_matrixALT_internal_relative_commutant_and_center (dims : Nat → Nat) {h : Nat} [NeZero h]
    (U : (k : Nat) → Fin h → UnitaryMatrix (dims k)) (hd : ∀ k, 0 < dims k)
    (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop) (κ : ℝ)
    (hgap : MatrixMarkovSpectralGap dims U hd L κ) :
    ∃ A : (k : Nat) → StarSubalgebra ℂ (CMatrix (dims k)),
      matrixRelativeExpectation dims U hd L hL = matrixQuotientExpectation dims A hd (L : Filter Nat) ∧
      matrixRelativeCommutant dims U (L : Filter Nat) = matrixInternalQuotient dims A (L : Filter Nat) ∧
      starSubalgebraCenter (matrixRelativeCommutant dims U (L : Filter Nat)) =
        matrixInternalQuotient dims (fun k => starSubalgebraCenter (A k)) (L : Filter Nat) := by
  obtain ⟨A, hexpect, hA⟩ := exists_matrixALT_internal_relative_commutant dims U hd L hL κ hgap
  refine ⟨A, hexpect, hA, ?_⟩
  rw [hA, matrixInternalQuotient_center dims A hd (L : Filter Nat)]

end ThomGame.Analysis
