module

public import ThomGame.Analysis.CStarContractiveLift
public import ThomGame.Analysis.MatrixInternalNormLift
public import ThomGame.Analysis.MatrixQuotientWOTIdentification
public import ThomGame.Analysis.MatrixInternalFiniteAlgebra

/-!
# Matrix representatives with exact operator norm bounds

The right norm clamp in the actual C-star product gives representatives
with the requested bound, with no factor two. Performing the same clamp
inside an internal product preserves every coordinate subalgebra.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter

variable {ι : Type*} (dims : ι → Nat) (hd : ∀ i, 0 < dims i) (U : Ultrafilter ι)

theorem exists_matrixRepresentative_bounded_exact
    (x : MatrixTracialQuotient dims (U : Filter ι))
    (K : ℝ) (hK : 0 ≤ K) (hx : ‖matrixLeftRepresentation dims hd U x‖ ≤ K) :
    ∃ B : BoundedMatrixSequence dims, (∀ i, matrixOpNorm (B.val i) ≤ K) ∧
      matrixQuotientMk dims (U : Filter ι) B = x := by
  obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims (U : Filter ι) x
  let p := (matrixOperatorProductEquiv dims hd).symm A
  have hp : matrixProductToFinite dims hd U p =
      matrixFiniteEmbedding dims hd U (matrixQuotientMk dims (U : Filter ι) A) := by
    rw [matrixProductToFinite_apply, show matrixOperatorProductEquiv dims hd p = A from
      (matrixOperatorProductEquiv dims hd).apply_symm_apply A]
  obtain ⟨b, hb, heq⟩ := exists_cstar_exact_norm_lift (matrixProductToFinite dims hd U) p K hK
    (by rw [hp, matrixFiniteEmbedding_norm]; exact hx)
  refine ⟨matrixOperatorProductEquiv dims hd b, ?_, ?_⟩
  · intro i
    exact (matrixOperatorProduct_apply_norm_le dims hd b i).trans hb
  · apply matrixFiniteEmbedding_injective dims hd U
    rw [← matrixProductToFinite_apply, ← hp]
    exact heq

theorem exists_matrixInternalRepresentative_bounded_exact
    (S : (i : ι) → StarSubalgebra ℂ (CMatrix (dims i)))
    (x : MatrixTracialQuotient dims (U : Filter ι))
    (hx : x ∈ matrixInternalQuotient dims S (U : Filter ι))
    (K : ℝ) (hK : 0 ≤ K) (hbound : ‖matrixLeftRepresentation dims hd U x‖ ≤ K) :
    ∃ B : BoundedMatrixSequence dims, (∀ i, B.val i ∈ S i) ∧
      (∀ i, matrixOpNorm (B.val i) ≤ K) ∧ matrixQuotientMk dims (U : Filter ι) B = x := by
  rw [← matrixInternalProductToQuotient_range dims S hd (U : Filter ι)] at hx
  obtain ⟨p, hp⟩ := hx
  have hpx : matrixInternalProductToFinite dims S hd U p = matrixFiniteEmbedding dims hd U x :=
    congrArg (matrixFiniteEmbedding dims hd U) hp
  obtain ⟨b, hb, heq⟩ := exists_cstar_exact_norm_lift (matrixInternalProductToFinite dims S hd U) p K hK
    (by rw [hpx, matrixFiniteEmbedding_norm]; exact hbound)
  refine ⟨matrixInternalProductToSequences dims S hd b,
    matrixInternalProductToSequences_mem dims S hd b, ?_, ?_⟩
  · intro i
    exact (matrixInternalProductToSequences_norm_le dims S hd b i).trans hb
  · apply matrixFiniteEmbedding_injective dims hd U
    exact heq.trans hpx

section NatIndex

variable (dims : Nat → Nat) (hd : ∀ n, 0 < dims n) (U : Ultrafilter Nat)

theorem exists_matrixFiniteRepresentative_bounded (hU : (U : Filter Nat) ≤ atTop)
    (T : MatrixFiniteOperatorAlgebra dims hd U) (K : ℝ) (hK : 0 ≤ K) (hT : ‖T‖ ≤ K) :
    ∃ B : BoundedMatrixSequence dims, (∀ n, matrixOpNorm (B.val n) ≤ K) ∧
      matrixFiniteEmbedding dims hd U (matrixQuotientMk dims (U : Filter Nat) B) = T := by
  obtain ⟨x, rfl⟩ := matrixFiniteEmbedding_surjective dims hd U hU T
  obtain ⟨B, hB, heq⟩ := exists_matrixRepresentative_bounded_exact dims hd U x K hK hT
  exact ⟨B, hB, congrArg (matrixFiniteEmbedding dims hd U) heq⟩

theorem exists_matrixInternalFiniteRepresentative_bounded
    (S : (n : Nat) → StarSubalgebra ℂ (CMatrix (dims n)))
    (T : MatrixFiniteOperatorAlgebra dims hd U) (hmem : T ∈ matrixInternalFiniteAlgebra dims S hd U)
    (K : ℝ) (hK : 0 ≤ K) (hT : ‖T‖ ≤ K) :
    ∃ B : BoundedMatrixSequence dims, (∀ n, B.val n ∈ S n) ∧
      (∀ n, matrixOpNorm (B.val n) ≤ K) ∧
      matrixFiniteEmbedding dims hd U (matrixQuotientMk dims (U : Filter Nat) B) = T := by
  obtain ⟨x, hx, heq⟩ := hmem
  change matrixFiniteEmbedding dims hd U x = T at heq
  obtain ⟨B, hBmem, hB, hxB⟩ := exists_matrixInternalRepresentative_bounded_exact dims hd U S x hx K hK
    (by rw [← matrixFiniteEmbedding_norm, heq]; exact hT)
  exact ⟨B, hBmem, hB, (congrArg (matrixFiniteEmbedding dims hd U) hxB).trans heq⟩

end NatIndex

end ThomGame.Analysis
