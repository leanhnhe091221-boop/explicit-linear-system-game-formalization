module

public import ThomGame.Analysis.MatrixALTQuotientRepresentatives
public import ThomGame.Analysis.MatrixInternalBlockCommutant
public import ThomGame.Analysis.MatrixMarkovBimodule

/-!
# Actual internal scalar diagonals for the ALT partitions

The scalar diagonal algebra lies in the original relative commutant,
and its full commutant consists exactly of internal block matrices.
The MASA assertion additionally requires the scalar approximation estimate.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

theorem matrixScalarGapPartition_internal_le_commutant {ι : Type*} (dims : ι → Nat) {h : Nat}
    (U : (k : ι) → Fin h → UnitaryMatrix (dims k)) (c : ℝ)
    (Q : (k : ι) → MatrixScalarGapPartition (U k) c) (L : Filter ι) :
    matrixInternalQuotient dims (fun k => matrixPartitionScalarAlgebra (Q k).E) L ≤
      matrixRelativeCommutant dims U L := by
  intro x hx
  obtain ⟨A, hA, rfl⟩ := (mem_matrixInternalQuotient dims _ L x).mp hx
  apply (mem_matrixRelativeCommutant_iff dims U L _).mpr
  intro j
  have hc : Commute (boundedUnitarySequence dims (fun k => U k j)) A := by
    apply Subtype.ext
    funext k
    exact ((Q k).scalar_commute (hA k) j).eq
  exact hc.map (matrixQuotientMk dims L)

theorem exists_matrixUltraproduct_ALT_scalar_diagonal (dims : Nat → Nat) {h : Nat} [NeZero h]
    (U : (k : Nat) → Fin h → UnitaryMatrix (dims k)) (hd : ∀ k, 0 < dims k)
    (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop) (κ : ℝ)
    (hgap : MatrixMarkovSpectralGap dims U hd L κ) :
    ∃ T : (k : Nat) → Fin (h + h) → UnitaryMatrix (dims k),
      ∃ Q : (k : Nat) → MatrixScalarGapPartition (T k) (κ ^ 2 / 2 ^ 28),
        (∀ k i, (Q k).E i ≠ 0) ∧ (∀ k, (Q k).n ≤ dims k) ∧
        Tendsto (fun k => ∑ j, hsNorm ((T k j).val - (Fin.append (U k) (U k) j).val) ^ 2)
          (L : Filter Nat) (𝓝 0) ∧
        (∀ j, matrixTupleClass dims T (L : Filter Nat) j =
          matrixTupleClass dims (fun k => Fin.append (U k) (U k)) (L : Filter Nat) j) ∧
        matrixInternalQuotient dims (fun k => matrixPartitionScalarAlgebra (Q k).E) (L : Filter Nat) ≤
          matrixRelativeCommutant dims U (L : Filter Nat) ∧
        StarSubalgebra.centralizer ℂ
          (matrixInternalQuotient dims (fun k => matrixPartitionScalarAlgebra (Q k).E) (L : Filter Nat) :
            Set (MatrixTracialQuotient dims (L : Filter Nat))) =
          matrixInternalQuotient dims (fun k => matrixPartitionBlockAlgebra (Q k).E) (L : Filter Nat) := by
  obtain ⟨T, Q, hnonzero, hcount, hperturb, hsame, _⟩ :=
    exists_matrixUltraproduct_ALT_nonzero_representatives dims U hd L hL κ hgap
  refine ⟨T, Q, hnonzero, hcount, hperturb, hsame, ?_, ?_⟩
  · intro x hx
    have hT := (mem_matrixRelativeCommutant_iff dims T (L : Filter Nat) x).mp
      (matrixScalarGapPartition_internal_le_commutant dims T _ Q (L : Filter Nat) hx)
    apply (mem_matrixRelativeCommutant_iff dims U (L : Filter Nat) x).mpr
    intro j
    have he := hT (Fin.castAdd h j)
    change Commute (matrixQuotientMk dims (L : Filter Nat)
      (boundedUnitarySequence dims (fun k => T k (Fin.castAdd h j)))) x at he
    rw [hsame] at he
    simpa only [Fin.append_left, matrixTupleClass] using he
  · exact matrixInternalDiagonal_centralizer dims (fun k => (Q k).E)
      (fun k => (Q k).projection) (fun k => (Q k).orthogonal) (fun k => (Q k).sum_one)
      (L : Filter Nat) hd

end ThomGame.Analysis
