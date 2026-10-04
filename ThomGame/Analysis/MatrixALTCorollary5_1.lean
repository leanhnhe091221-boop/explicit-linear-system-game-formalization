module

public import ThomGame.Analysis.MatrixALTScalarMASA
public import ThomGame.Analysis.MatrixPerturbedDiagonalExpectation
public import ThomGame.Analysis.MatrixMarkovCompletelyPositive
public import ThomGame.Analysis.MatrixMarkovBimodule

/-!
# ALT Corollary 5.1 with actual completely positive maps

The same corrected Markov powers induce the original conditional
expectation, satisfy all coordinate algebraic properties, and converge
uniformly to scalars on the corners. The actual internal scalar
diagonal is a MASA of the original relative commutant.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder CStarAlgebra

theorem exists_matrixUltraproduct_ALT_corollary5_1 (dims : Nat → Nat) {h : Nat} [NeZero h]
    (U : (k : Nat) → Fin h → UnitaryMatrix (dims k)) (hd : ∀ k, 0 < dims k)
    (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop) (κ : ℝ)
    (hgap : MatrixMarkovSpectralGap dims U hd L κ) :
    ∃ T : (k : Nat) → Fin (h + h) → UnitaryMatrix (dims k),
      ∃ Q : (k : Nat) → MatrixScalarGapPartition (T k) (κ ^ 2 / 2 ^ 28),
      ∃ N : Nat → Nat, ∃ Ψ : (k : Nat) → CMatrix (dims k) →CP CMatrix (dims k),
        (∀ k i, (Q k).E i ≠ 0) ∧ (∀ k, (Q k).n ≤ dims k) ∧
        Tendsto (fun k => ∑ j, hsNorm ((T k j).val - (Fin.append (U k) (U k) j).val) ^ 2)
          (L : Filter Nat) (𝓝 0) ∧
        (∀ j, matrixTupleClass dims T (L : Filter Nat) j =
          matrixTupleClass dims (fun k => Fin.append (U k) (U k)) (L : Filter Nat) j) ∧
        (∀ k, 0 < N k) ∧ Tendsto N (L : Filter Nat) atTop ∧
        (∀ k, (Ψ k).toLinearMap = (matrixUniformMarkovPower dims T hd N).toLinearMap k) ∧
        (∀ k, Ψ k 1 = 1) ∧
        (∀ k X, normalizedTrace (Ψ k X) = normalizedTrace X) ∧
        (∀ k A X B, A ∈ matrixPartitionScalarAlgebra (Q k).E →
          B ∈ matrixPartitionScalarAlgebra (Q k).E → Ψ k (A * X * B) = A * Ψ k X * B) ∧
        (∀ k X Y, normalizedTrace (star (Ψ k X) * Y) = normalizedTrace (star X * Ψ k Y)) ∧
        (matrixUniformMarkovPower dims T hd N).quotientMap (L : Filter Nat) =
          matrixRelativeExpectation dims U hd L hL ∧
        Tendsto (matrixScalarCornerErrorSequence dims T hd Q N) (L : Filter Nat) (𝓝 0) ∧
        matrixInternalQuotient dims (fun k => matrixPartitionScalarAlgebra (Q k).E) (L : Filter Nat) ≤
          matrixRelativeCommutant dims U (L : Filter Nat) ∧
        (StarSubalgebra.centralizer ℂ
          (matrixInternalQuotient dims (fun k => matrixPartitionScalarAlgebra (Q k).E) (L : Filter Nat) :
            Set (MatrixTracialQuotient dims (L : Filter Nat))) ⊓ matrixRelativeCommutant dims U (L : Filter Nat) =
          matrixInternalQuotient dims (fun k => matrixPartitionScalarAlgebra (Q k).E) (L : Filter Nat)) := by
  obtain ⟨T, Q, hne, hcount, hperturb, hsame, hDC, hmasa, hcorner⟩ :=
    exists_matrixUltraproduct_ALT_masa dims U hd L hL κ hgap
  obtain ⟨N, hpos, hN, _, _, hE⟩ :=
    exists_matrixALT_corrected_power_expectation dims U hd L hL κ hgap T hperturb
  let Ψ := fun k => matrixMarkovPowerCP (T k) (N k)
  let (k : Nat) : NeZero (dims k) := ⟨Nat.ne_of_gt (hd k)⟩
  refine ⟨T, Q, N, Ψ, hne, hcount, hperturb, hsame, hpos, hN,
    (fun _ => rfl), ?_, ?_, ?_, ?_, hE, hcorner N hN, hDC, hmasa⟩
  · intro k
    exact matrixLazyMarkov_pow_one (T k) (N k)
  · intro k X
    exact matrixLazyMarkov_pow_trace (T k) (N k) X
  · intro k A X B hA hB
    exact (Q k).markov_pow_bimodule (N k) A X B hA hB
  · intro k X Y
    exact matrixLazyMarkov_pow_pairing (T k) (N k) X Y

end ThomGame.Analysis
