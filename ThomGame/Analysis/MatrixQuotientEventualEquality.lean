module

public import ThomGame.Analysis.MatrixInternalSequences

/-!
# Changing coordinates off a filter-large set preserves the actual quotient

Bounded representatives are cut off by zero on the exceptional set.
This preserves their classes and proves eventual inclusion and equality
of internal coordinate algebras on the original index set.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable {ι : Type*} (dims : ι → Nat)

theorem matrixQuotientMk_eq_of_eventually_eq (L : Filter ι) (A B : BoundedMatrixSequence dims)
    (hAB : ∀ᶠ i in L, A.val i = B.val i) : matrixQuotientMk dims L A = matrixQuotientMk dims L B := by
  apply (matrixQuotientMk_eq_iff dims L A B).mpr
  have he : (fun i => hsNorm (A.val i - B.val i)) =ᶠ[L] fun _ => (0 : ℝ) :=
    hAB.mono fun i hi => by
      change hsNorm (A.val i - B.val i) = 0
      rw [hi, sub_self, hsNorm_zero]
  exact tendsto_const_nhds.congr' he.symm

noncomputable def matrixSequenceSetCut (s : Set ι) (A : BoundedMatrixSequence dims) :
    BoundedMatrixSequence dims := by
  classical
  refine ⟨fun i => if i ∈ s then A.val i else 0, ?_⟩
  obtain ⟨K, hK, hA⟩ := BoundedMatrixSequence.bound dims A
  refine ⟨K, hK, fun i => ?_⟩
  change matrixOpNorm (if i ∈ s then A.val i else 0) ≤ K
  split_ifs
  · exact hA i
  · simpa only [matrixOpNorm_zero] using hK

theorem matrixSequenceSetCut_of_mem (s : Set ι) (A : BoundedMatrixSequence dims) {i : ι} (hi : i ∈ s) :
    (matrixSequenceSetCut dims s A).val i = A.val i := by simp [matrixSequenceSetCut, hi]

theorem matrixSequenceSetCut_of_not_mem (s : Set ι) (A : BoundedMatrixSequence dims) {i : ι} (hi : i ∉ s) :
    (matrixSequenceSetCut dims s A).val i = 0 := by simp [matrixSequenceSetCut, hi]

theorem matrixSequenceSetCut_mk (L : Filter ι) (s : Set ι) (hs : s ∈ L) (A : BoundedMatrixSequence dims) :
    matrixQuotientMk dims L (matrixSequenceSetCut dims s A) = matrixQuotientMk dims L A :=
  matrixQuotientMk_eq_of_eventually_eq dims L _ A
    ((show ∀ᶠ i in L, i ∈ s from hs).mono fun _ hi => matrixSequenceSetCut_of_mem dims s A hi)

theorem matrixInternalQuotient_le_of_eventually_le
    (A B : (i : ι) → StarSubalgebra ℂ (CMatrix (dims i))) (L : Filter ι)
    (hAB : ∀ᶠ i in L, A i ≤ B i) : matrixInternalQuotient dims A L ≤ matrixInternalQuotient dims B L := by
  intro x hx
  obtain ⟨X, hX, rfl⟩ := (mem_matrixInternalQuotient dims A L x).mp hx
  let s : Set ι := {i | A i ≤ B i}
  refine ⟨matrixSequenceSetCut dims s X, ?_, matrixSequenceSetCut_mk dims L s hAB X⟩
  intro i
  by_cases hi : i ∈ s
  · rw [matrixSequenceSetCut_of_mem dims s X hi]
    exact hi (hX i)
  · rw [matrixSequenceSetCut_of_not_mem dims s X hi]
    exact (B i).zero_mem

theorem matrixInternalQuotient_eq_of_eventually_eq
    (A B : (i : ι) → StarSubalgebra ℂ (CMatrix (dims i))) (L : Filter ι)
    (hAB : ∀ᶠ i in L, A i = B i) : matrixInternalQuotient dims A L = matrixInternalQuotient dims B L :=
  le_antisymm (matrixInternalQuotient_le_of_eventually_le dims A B L (hAB.mono fun _ h => h.le))
    (matrixInternalQuotient_le_of_eventually_le dims B A L (hAB.mono fun _ h => h.ge))

end ThomGame.Analysis
