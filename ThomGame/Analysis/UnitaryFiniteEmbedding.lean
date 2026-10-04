module

public import ThomGame.Analysis.UnitaryQuotientEmbedding
public import ThomGame.Analysis.MatrixFiniteTraceProperties

/-!
# The actual unitary sequence quotient in the finite operator algebra

Compose the proved injective unitary map into the matrix star-algebra
quotient with its faithful representation in the weakly closed finite
operator algebra. The construction preserves the normalized trace on
every actual unitary sequence representative.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter

variable {ι : Type*} (dims : ι → Nat) (hd : ∀ i, 0 < dims i) (U : Ultrafilter ι)

noncomputable def matrixFiniteUnitaryHom :
    unitary (MatrixTracialQuotient dims (U : Filter ι)) →*
      unitary (MatrixFiniteOperatorAlgebra dims hd U) where
  toFun u := ⟨matrixFiniteEmbedding dims hd U u.val,
    Unitary.map_mem (matrixFiniteEmbedding dims hd U) u.property⟩
  map_one' := Subtype.ext (map_one (matrixFiniteEmbedding dims hd U))
  map_mul' a b := Subtype.ext (map_mul (matrixFiniteEmbedding dims hd U) a.val b.val)

theorem matrixFiniteUnitaryHom_injective : Function.Injective (matrixFiniteUnitaryHom dims hd U) := by
  intro a b h
  apply Subtype.ext
  exact matrixFiniteEmbedding_injective dims hd U (congrArg Subtype.val h)

noncomputable def unitaryQuotientFiniteEmbedding :
    UnitarySequenceQuotient dims (U : Filter ι) →* unitary (MatrixFiniteOperatorAlgebra dims hd U) :=
  (matrixFiniteUnitaryHom dims hd U).comp (unitaryQuotientEmbedding dims (U : Filter ι))

theorem unitaryQuotientFiniteEmbedding_injective :
    Function.Injective (unitaryQuotientFiniteEmbedding dims hd U) :=
  (matrixFiniteUnitaryHom_injective dims hd U).comp (unitaryQuotientEmbedding_injective dims (U : Filter ι))

theorem unitaryQuotientFiniteEmbedding_mk (V : UnitarySequence dims) :
    (unitaryQuotientFiniteEmbedding dims hd U (unitarySequenceMk dims (U : Filter ι) V)).val =
      matrixFiniteEmbedding dims hd U (matrixQuotientMk dims (U : Filter ι) (boundedUnitarySequence dims V)) := rfl

theorem unitaryQuotientFiniteEmbedding_trace (V : UnitarySequence dims) :
    matrixFiniteTrace dims hd U
        (unitaryQuotientFiniteEmbedding dims hd U (unitarySequenceMk dims (U : Filter ι) V)).val =
      matrixSequenceUltratrace dims U (boundedUnitarySequence dims V) := by
  rw [unitaryQuotientFiniteEmbedding_mk, matrixFiniteTrace_embedding, matrixUltratrace_mk]

end ThomGame.Analysis
