module

public import ThomGame.Analysis.MatrixTracialAlgebra
public import ThomGame.Analysis.UnitarySequenceQuotient

/-!
# The unitary sequence quotient embeds in the actual matrix quotient

Every unitary sequence is uniformly operator-bounded. Its image in the
matrix star algebra is unitary, and the kernel is exactly the previously
defined subgroup of 2-null unitary sequences. The induced map is injective.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable {ι : Type*} (dims : ι → Nat) (L : Filter ι)

def unitarySequenceToAlgebra : UnitarySequence dims →* unitary (MatrixTracialQuotient dims L) where
  toFun U := ⟨matrixQuotientMk dims L (boundedUnitarySequence dims U), by
    constructor
    · rw [matrixQuotientMk_star, ← map_mul, boundedUnitarySequence_star_mul, map_one]
    · rw [matrixQuotientMk_star, ← map_mul, boundedUnitarySequence_mul_star, map_one]⟩
  map_one' := Subtype.ext (by change matrixQuotientMk dims L 1 = 1; exact map_one _)
  map_mul' U V := Subtype.ext (by
    change matrixQuotientMk dims L (boundedUnitarySequence dims (fun i => U i * V i)) = _
    rw [boundedUnitarySequence_mul, map_mul]
    rfl)

theorem unitarySequenceToAlgebra_eq_one_iff (U : UnitarySequence dims) :
    unitarySequenceToAlgebra dims L U = 1 ↔
      Tendsto (fun i => unitaryLength (U i)) L (𝓝 0) := by
  rw [Subtype.ext_iff]
  change matrixQuotientMk dims L (boundedUnitarySequence dims U) = matrixQuotientMk dims L 1 ↔ _
  exact matrixQuotientMk_eq_iff dims L _ _

def unitaryQuotientEmbedding :
    UnitarySequenceQuotient dims L →* unitary (MatrixTracialQuotient dims L) :=
  QuotientGroup.lift (nullUnitarySubgroup dims L) (unitarySequenceToAlgebra dims L)
    (fun U hU => (unitarySequenceToAlgebra_eq_one_iff dims L U).mpr hU)

@[simp] theorem unitaryQuotientEmbedding_mk (U : UnitarySequence dims) :
    unitaryQuotientEmbedding dims L (unitarySequenceMk dims L U) = unitarySequenceToAlgebra dims L U := rfl

theorem unitaryQuotientEmbedding_injective : Function.Injective (unitaryQuotientEmbedding dims L) := by
  apply (unitaryQuotientEmbedding dims L).ker_eq_bot_iff.mp
  apply le_antisymm ?_ bot_le
  intro x hx
  change x = 1
  obtain ⟨U, rfl⟩ := QuotientGroup.mk_surjective x
  apply (unitarySequenceMk_eq_one_iff dims L U).mpr
  exact (unitarySequenceToAlgebra_eq_one_iff dims L U).mp hx

end ThomGame.Analysis
