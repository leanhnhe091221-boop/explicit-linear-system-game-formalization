module

public import ThomGame.Analysis.MatrixInternalScalarMASA
public import ThomGame.Analysis.MatrixUniformCornerDecay

/-!
# The ALT scalar diagonal is a MASA in the original commutant

The actual corrected tuple represents the original doubled tuple.
Its scalar diagonal is maximal abelian in the original relative
commutant, and every diverging sequence of its Markov powers has
uniformly vanishing corner scalar error.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology BigOperators Matrix.Norms.L2Operator

theorem matrixRelativeCommutant_eq_of_tupleClass_eq {ι : Type*} (dims : ι → Nat) {h : Nat}
    (U V : (k : ι) → Fin h → UnitaryMatrix (dims k)) (L : Filter ι)
    (hUV : ∀ j, matrixTupleClass dims U L j = matrixTupleClass dims V L j) :
    matrixRelativeCommutant dims U L = matrixRelativeCommutant dims V L := by
  ext x
  simp only [mem_matrixRelativeCommutant_iff, hUV]

theorem matrixRelativeCommutant_append_self {ι : Type*} (dims : ι → Nat) {h : Nat}
    (U : (k : ι) → Fin h → UnitaryMatrix (dims k)) (L : Filter ι) :
    matrixRelativeCommutant dims (fun k => Fin.append (U k) (U k)) L = matrixRelativeCommutant dims U L := by
  ext x
  rw [mem_matrixRelativeCommutant_iff, mem_matrixRelativeCommutant_iff]
  constructor
  · intro hx j
    simpa only [matrixTupleClass, Fin.append_left] using hx (Fin.castAdd h j)
  · intro hx j
    refine Fin.addCases ?_ ?_ j
    · intro a
      simpa only [matrixTupleClass, Fin.append_left] using hx a
    · intro a
      simpa only [matrixTupleClass, Fin.append_right] using hx a

theorem matrixScalarGapPartition_internal_maximal {ι : Type*} (dims : ι → Nat) {h : Nat}
    (U : (k : ι) → Fin h → UnitaryMatrix (dims k)) (hd : ∀ k, 0 < dims k)
    (c : ℝ) (Q : (k : ι) → MatrixScalarGapPartition (U k) c) (L : Filter ι)
    (hc : 0 < c) (hne : ∀ k i, (Q k).E i ≠ 0)
    (B : StarSubalgebra ℂ (MatrixTracialQuotient dims L))
    (hDB : matrixInternalQuotient dims (fun k => matrixPartitionScalarAlgebra (Q k).E) L ≤ B)
    (hBC : B ≤ matrixRelativeCommutant dims U L)
    (habel : ∀ x ∈ B, ∀ y ∈ B, Commute x y) :
    B = matrixInternalQuotient dims (fun k => matrixPartitionScalarAlgebra (Q k).E) L := by
  apply le_antisymm _ hDB
  intro x hx
  rw [← matrixScalarGapPartition_internal_masa dims U hd c Q L hc hne]
  refine ⟨?_, hBC hx⟩
  exact (StarSubalgebra.mem_centralizer_iff ℂ).2 (fun y hy =>
    ⟨(habel y (hDB hy) x hx).eq, (habel (star y) (B.star_mem' (hDB hy)) x hx).eq⟩)

theorem exists_matrixUltraproduct_ALT_masa (dims : Nat → Nat) {h : Nat} [NeZero h]
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
        (StarSubalgebra.centralizer ℂ
          (matrixInternalQuotient dims (fun k => matrixPartitionScalarAlgebra (Q k).E) (L : Filter Nat) :
            Set (MatrixTracialQuotient dims (L : Filter Nat))) ⊓ matrixRelativeCommutant dims U (L : Filter Nat) =
          matrixInternalQuotient dims (fun k => matrixPartitionScalarAlgebra (Q k).E) (L : Filter Nat)) ∧
        ∀ N : Nat → Nat, Tendsto N (L : Filter Nat) atTop →
          Tendsto (matrixScalarCornerErrorSequence dims T hd Q N) (L : Filter Nat) (𝓝 0) := by
  obtain ⟨T, Q, hne, hcount, hperturb, hsame, hDC, _⟩ :=
    exists_matrixUltraproduct_ALT_scalar_diagonal dims U hd L hL κ hgap
  have hc₀ : 0 < κ ^ 2 / (2 : ℝ) ^ 28 := div_pos (sq_pos_of_pos hgap.1) (by positivity)
  have hc₁ : κ ^ 2 / (2 : ℝ) ^ 28 ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    calc
      κ ^ 2 ≤ (1 : ℝ) ^ 2 := (sq_le_sq₀ hgap.1.le zero_le_one).mpr hgap.2.1.le
      _ ≤ 1 * (2 : ℝ) ^ 28 := by norm_num
  have hC : matrixRelativeCommutant dims T (L : Filter Nat) = matrixRelativeCommutant dims U (L : Filter Nat) :=
    (matrixRelativeCommutant_eq_of_tupleClass_eq dims T (fun k => Fin.append (U k) (U k)) (L : Filter Nat) hsame).trans
      (matrixRelativeCommutant_append_self dims U (L : Filter Nat))
  refine ⟨T, Q, hne, hcount, hperturb, hsame, hDC, ?_, ?_⟩
  · rw [← hC]
    exact matrixScalarGapPartition_internal_masa dims T hd _ Q (L : Filter Nat) hc₀ hne
  · intro N hN
    exact matrixScalarCornerErrorSequence_tendsto_zero dims T hd Q N hc₀ hc₁ hne (L : Filter Nat) hN

end ThomGame.Analysis
