module

public import ThomGame.Analysis.MatrixThomTheorem4_2
public import ThomGame.Analysis.MatrixFiniteNearInclusion
public import ThomGame.Analysis.MatrixFiniteRelativeExpectation
public import ThomGame.Analysis.UnitaryFiniteEmbedding

/-!
# Thom Theorem 4.2 in the actual finite operator model

The faithful embedding preserves conjugation and reflects the stated
anchor. Hence the quotient theorem applies to the actual internal
operator algebras, with their given unitary representatives.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter

variable (dims : Nat → Nat)
    (A D : (n : Nat) → StarSubalgebra ℂ (CMatrix (dims n)))
    (hd : ∀ n, 0 < dims n) (L : Ultrafilter Nat)

theorem matrixInternalFinite_unitaryPullback_eq
    (U : (n : Nat) → UnitaryMatrix (dims n)) :
    matrixInternalFiniteAlgebra dims (fun n => matrixUnitaryPullbackAlgebra (A n) (U n)) hd L =
      (matrixInternalFiniteAlgebra dims A hd L).map
        (Unitary.conjStarAlgAut ℂ (MatrixFiniteOperatorAlgebra dims hd L)
          (matrixFiniteUnitaryHom dims hd L (unitarySequenceToAlgebra dims (L : Filter Nat) U))).symm.toStarAlgHom := by
  simp only [matrixInternalFiniteAlgebra, matrixInternal_unitaryPullback_eq, StarSubalgebra.map_map]
  congr 1
  apply StarAlgHom.ext
  intro x
  change matrixFiniteEmbedding dims hd L
      (star (unitarySequenceToAlgebra dims (L : Filter Nat) U).val * x *
        (unitarySequenceToAlgebra dims (L : Filter Nat) U).val) =
    star (matrixFiniteEmbedding dims hd L (unitarySequenceToAlgebra dims (L : Filter Nat) U).val) *
      matrixFiniteEmbedding dims hd L x *
      matrixFiniteEmbedding dims hd L (unitarySequenceToAlgebra dims (L : Filter Nat) U).val
  rw [map_mul, map_mul, map_star]

theorem matrixThom_finite_theorem_4_2_of_internal_inclusions
    (hDA : ∀ n, D n ≤ A n) {h : Nat} (U : (n : Nat) → Fin h → UnitaryMatrix (dims n))
    (hU : ∀ n j X, X ∈ D n → (U n j).val * X = X * (U n j).val)
    (hincl : ∀ j, matrixInternalFiniteAlgebra dims
      (fun n => matrixUnitaryPullbackAlgebra (A n) (U n j)) hd L ≤ matrixInternalFiniteAlgebra dims A hd L)
    (hanchor : matrixInternalFiniteAlgebra dims A hd L ⊓ matrixFiniteRelativeCommutant dims U hd L =
      matrixInternalFiniteAlgebra dims D hd L) :
    ∀ j, matrixInternalFiniteAlgebra dims (fun n => matrixUnitaryPullbackAlgebra (A n) (U n j)) hd L =
      matrixInternalFiniteAlgebra dims A hd L := by
  let : ∀ n, NeZero (dims n) := fun n => ⟨ne_of_gt (hd n)⟩
  have ha : matrixInternalQuotient dims A (L : Filter Nat) ⊓ matrixRelativeCommutant dims U (L : Filter Nat) =
      matrixInternalQuotient dims D (L : Filter Nat) := by
    ext x
    have he := SetLike.ext_iff.mp hanchor (matrixFiniteEmbedding dims hd L x)
    simpa only [StarSubalgebra.mem_inf, matrixFiniteEmbedding_mem_internal_iff,
      matrixFiniteEmbedding_mem_relativeCommutant_iff] using he
  have hi j := (matrixInternalFiniteAlgebra_le_iff dims _ A hd L).mp (hincl j)
  have he := matrixThom_theorem_4_2_of_internal_inclusions dims A D hDA U hU (L : Filter Nat) hi ha
  intro j
  exact congrArg (StarSubalgebra.map (matrixFiniteEmbedding dims hd L)) (he j)

theorem matrixThom_finite_theorem_4_2
    (hDA : ∀ n, D n ≤ A n) {h : Nat} (U : (n : Nat) → Fin h → UnitaryMatrix (dims n))
    (hU : ∀ n j X, X ∈ D n → (U n j).val * X = X * (U n j).val)
    (hincl : ∀ j, (matrixInternalFiniteAlgebra dims A hd L).map
      (Unitary.conjStarAlgAut ℂ (MatrixFiniteOperatorAlgebra dims hd L)
        (matrixFiniteUnitaryHom dims hd L
          (unitarySequenceToAlgebra dims (L : Filter Nat) (fun n => U n j)))).symm.toStarAlgHom ≤
      matrixInternalFiniteAlgebra dims A hd L)
    (hanchor : matrixInternalFiniteAlgebra dims A hd L ⊓ matrixFiniteRelativeCommutant dims U hd L =
      matrixInternalFiniteAlgebra dims D hd L) :
    ∀ j, (matrixInternalFiniteAlgebra dims A hd L).map
      (Unitary.conjStarAlgAut ℂ (MatrixFiniteOperatorAlgebra dims hd L)
        (matrixFiniteUnitaryHom dims hd L
          (unitarySequenceToAlgebra dims (L : Filter Nat) (fun n => U n j)))).symm.toStarAlgHom =
      matrixInternalFiniteAlgebra dims A hd L := by
  have hi j : matrixInternalFiniteAlgebra dims
      (fun n => matrixUnitaryPullbackAlgebra (A n) (U n j)) hd L ≤ matrixInternalFiniteAlgebra dims A hd L := by
    rw [matrixInternalFinite_unitaryPullback_eq]
    exact hincl j
  intro j
  rw [← matrixInternalFinite_unitaryPullback_eq]
  exact matrixThom_finite_theorem_4_2_of_internal_inclusions dims A D hd L hDA U hU hi hanchor j

end ThomGame.Analysis
