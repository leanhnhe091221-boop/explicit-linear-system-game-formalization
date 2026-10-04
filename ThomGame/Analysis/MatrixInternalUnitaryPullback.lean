module

public import ThomGame.Analysis.MatrixUnitaryPullbackBlocks
public import ThomGame.Analysis.MatrixInternalSequences
public import ThomGame.Analysis.UnitaryQuotientEmbedding

/-!
# Unitary pullback commutes with the actual internal quotient

Both directions use uniformly bounded conjugate representatives. The
equality identifies the coordinate pullback with conjugation by the
specified unitary element of the matrix tracial quotient.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix Filter

variable {ι : Type*} (dims : ι → Nat)
    (A : (n : ι) → StarSubalgebra ℂ (CMatrix (dims n)))
    (U : (n : ι) → UnitaryMatrix (dims n)) (L : Filter ι)

theorem matrixInternal_unitaryPullback_eq :
    matrixInternalQuotient dims (fun n => matrixUnitaryPullbackAlgebra (A n) (U n)) L =
      (matrixInternalQuotient dims A L).map
        (Unitary.conjStarAlgAut ℂ (MatrixTracialQuotient dims L)
          (unitarySequenceToAlgebra dims L U)).symm.toStarAlgHom := by
  let V := boundedUnitarySequence dims U
  let e := Unitary.conjStarAlgAut ℂ (MatrixTracialQuotient dims L) (unitarySequenceToAlgebra dims L U)
  apply le_antisymm
  · intro z hz
    obtain ⟨X, hX, rfl⟩ := (mem_matrixInternalQuotient dims _ L z).mp hz
    let Y := V * X * star V
    have hYA : ∀ n, Y.val n ∈ A n := fun n =>
      (matrixUnitaryPullbackHom (A n) (U n) ⟨X.val n, hX n⟩).property
    refine ⟨matrixQuotientMk dims L Y, (mem_matrixInternalQuotient dims A L _).mpr ⟨Y, hYA, rfl⟩, ?_⟩
    change e.symm (matrixQuotientMk dims L Y) = matrixQuotientMk dims L X
    apply e.injective
    change e (e.symm (matrixQuotientMk dims L Y)) = e (matrixQuotientMk dims L X)
    rw [StarAlgEquiv.apply_symm_apply]
    change matrixQuotientMk dims L (V * X * star V) =
      matrixQuotientMk dims L V * matrixQuotientMk dims L X * star (matrixQuotientMk dims L V)
    rw [map_mul, map_mul, matrixQuotientMk_star]
  · rintro z ⟨w, hw, rfl⟩
    obtain ⟨Y, hY, rfl⟩ := (mem_matrixInternalQuotient dims A L w).mp hw
    let X := star V * Y * V
    have hXB : ∀ n, X.val n ∈ matrixUnitaryPullbackAlgebra (A n) (U n) :=
      fun n => ⟨Y.val n, hY n, rfl⟩
    refine (mem_matrixInternalQuotient dims _ L _).mpr ⟨X, hXB, ?_⟩
    change matrixQuotientMk dims L (star V * Y * V) = e.symm (matrixQuotientMk dims L Y)
    change matrixQuotientMk dims L (star V * Y * V) =
      star (matrixQuotientMk dims L V) * matrixQuotientMk dims L Y * matrixQuotientMk dims L V
    rw [map_mul, map_mul, matrixQuotientMk_star]

end ThomGame.Analysis
