module

public import ThomGame.Analysis.MatrixUnitaryCorrection
public import ThomGame.Analysis.UnitaryQuotientEmbedding

/-!
# Exact unitary representatives in the matrix tracial quotient

Gram defects tending to zero admit actual coordinate unitary corrections.
Consequently the unitary sequence quotient is the full unitary group of
the matrix tracial quotient, for every filter and positive dimension sequence.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter Matrix
open scoped Topology

variable {ι : Type*} (dims : ι → Nat) (hd : ∀ i, 0 < dims i) (L : Filter ι)

include hd

theorem exists_unitarySequence_close_of_gram (A : BoundedMatrixSequence dims)
    (hgram : Tendsto (fun i => hsNorm ((A.val i)ᴴ * A.val i - 1)) L (𝓝 0)) :
    ∃ U : UnitarySequence dims, Tendsto (fun i => hsNorm (A.val i - (U i).val)) L (𝓝 0) := by
  classical
  let (i : ι) : NeZero (dims i) := ⟨Nat.ne_of_gt (hd i)⟩
  choose U hU using fun i => exists_matrixUnitary_close_of_gram (A.val i)
  exact ⟨U, squeeze_zero (fun i => hsNorm_nonneg _) hU hgram⟩

theorem exists_matrixQuotient_unitary_lift (u : unitary (MatrixTracialQuotient dims L)) :
    ∃ U : UnitarySequence dims, matrixQuotientMk dims L (boundedUnitarySequence dims U) = u.val := by
  obtain ⟨A, hA⟩ := matrixQuotientMk_surjective dims L u.val
  have he : matrixQuotientMk dims L (star A * A) = matrixQuotientMk dims L 1 := by
    rw [map_mul, ← matrixQuotientMk_star, hA, map_one]
    exact u.property.1
  have hgram := (matrixQuotientMk_eq_iff dims L (star A * A) 1).mp he
  obtain ⟨U, hU⟩ := exists_unitarySequence_close_of_gram dims hd L A hgram
  exact ⟨U, ((matrixQuotientMk_eq_iff dims L A (boundedUnitarySequence dims U)).mpr hU).symm.trans hA⟩

theorem unitarySequenceToAlgebra_surjective : Function.Surjective (unitarySequenceToAlgebra dims L) := by
  intro u
  obtain ⟨U, hU⟩ := exists_matrixQuotient_unitary_lift dims hd L u
  exact ⟨U, Subtype.ext hU⟩

theorem unitaryQuotientEmbedding_surjective : Function.Surjective (unitaryQuotientEmbedding dims L) := by
  intro u
  obtain ⟨U, hU⟩ := unitarySequenceToAlgebra_surjective dims hd L u
  exact ⟨unitarySequenceMk dims L U, hU⟩

noncomputable def unitaryQuotientEquiv :
    UnitarySequenceQuotient dims L ≃* unitary (MatrixTracialQuotient dims L) :=
  MulEquiv.ofBijective (unitaryQuotientEmbedding dims L)
    ⟨unitaryQuotientEmbedding_injective dims L, unitaryQuotientEmbedding_surjective dims hd L⟩

@[simp] theorem unitaryQuotientEquiv_apply (x : UnitarySequenceQuotient dims L) :
    unitaryQuotientEquiv dims hd L x = unitaryQuotientEmbedding dims L x := rfl

@[simp] theorem unitaryQuotientEquiv_mk (U : UnitarySequence dims) :
    unitaryQuotientEquiv dims hd L (unitarySequenceMk dims L U) = unitarySequenceToAlgebra dims L U := rfl

end ThomGame.Analysis
