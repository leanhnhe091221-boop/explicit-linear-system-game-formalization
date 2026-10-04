module

public import ThomGame.Analysis.MatrixUnitaryLifting
public import ThomGame.Analysis.UnitaryFiniteEmbedding
public import ThomGame.Analysis.MatrixQuotientWOTIdentification

/-!
# The unitary sequence quotient is the full finite-algebra unitary group

The actual matrix quotient and its finite weakly closed representation
are already isomorphic. Exact unitary lifting makes both previous unitary
embeddings surjective, with the same representative and trace formulas.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter

variable (dims : Nat → Nat) (hd : ∀ n, 0 < dims n) (L : Ultrafilter Nat)
  (hL : (L : Filter Nat) ≤ atTop)

include hL in
theorem matrixFiniteUnitaryHom_surjective : Function.Surjective (matrixFiniteUnitaryHom dims hd L) := by
  intro u
  let e := matrixFiniteEquiv dims hd L hL
  let x : unitary (MatrixTracialQuotient dims (L : Filter Nat)) :=
    ⟨e.symm u.val, Unitary.map_mem e.symm u.property⟩
  refine ⟨x, Subtype.ext ?_⟩
  change e (e.symm u.val) = u.val
  exact e.apply_symm_apply u.val

noncomputable def matrixFiniteUnitaryEquiv :
    unitary (MatrixTracialQuotient dims (L : Filter Nat)) ≃* unitary (MatrixFiniteOperatorAlgebra dims hd L) :=
  MulEquiv.ofBijective (matrixFiniteUnitaryHom dims hd L)
    ⟨matrixFiniteUnitaryHom_injective dims hd L, matrixFiniteUnitaryHom_surjective dims hd L hL⟩

@[simp] theorem matrixFiniteUnitaryEquiv_apply (u : unitary (MatrixTracialQuotient dims (L : Filter Nat))) :
    matrixFiniteUnitaryEquiv dims hd L hL u = matrixFiniteUnitaryHom dims hd L u := rfl

include hL in
theorem unitaryQuotientFiniteEmbedding_surjective :
    Function.Surjective (unitaryQuotientFiniteEmbedding dims hd L) :=
  (matrixFiniteUnitaryHom_surjective dims hd L hL).comp (unitaryQuotientEmbedding_surjective dims hd (L : Filter Nat))

noncomputable def unitaryQuotientFiniteEquiv :
    UnitarySequenceQuotient dims (L : Filter Nat) ≃* unitary (MatrixFiniteOperatorAlgebra dims hd L) :=
  MulEquiv.ofBijective (unitaryQuotientFiniteEmbedding dims hd L)
    ⟨unitaryQuotientFiniteEmbedding_injective dims hd L, unitaryQuotientFiniteEmbedding_surjective dims hd L hL⟩

@[simp] theorem unitaryQuotientFiniteEquiv_apply (u : UnitarySequenceQuotient dims (L : Filter Nat)) :
    unitaryQuotientFiniteEquiv dims hd L hL u = unitaryQuotientFiniteEmbedding dims hd L u := rfl

@[simp] theorem unitaryQuotientFiniteEquiv_mk (U : UnitarySequence dims) :
    (unitaryQuotientFiniteEquiv dims hd L hL (unitarySequenceMk dims (L : Filter Nat) U)).val =
      matrixFiniteEmbedding dims hd L (matrixQuotientMk dims (L : Filter Nat) (boundedUnitarySequence dims U)) := rfl

theorem unitaryQuotientFiniteEquiv_trace (U : UnitarySequence dims) :
    matrixFiniteTrace dims hd L
        (unitaryQuotientFiniteEquiv dims hd L hL (unitarySequenceMk dims (L : Filter Nat) U)).val =
      matrixSequenceUltratrace dims L (boundedUnitarySequence dims U) :=
  unitaryQuotientFiniteEmbedding_trace dims hd L U

end ThomGame.Analysis
