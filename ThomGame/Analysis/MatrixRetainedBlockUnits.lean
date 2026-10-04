module

public import ThomGame.Analysis.MatrixRetainedBlockRange
public import ThomGame.Analysis.MatrixStarBlockScalarCoordinates

/-!
# Retained matrix units and scalar coordinates in the actual range

The new units are images of the original, labelled units. Thus their
ranks, supports and scalar combinations keep their original meaning.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {n m : Nat} (p : Fin n → Nat) (keep : Fin n → Prop) [DecidablePred keep]
    (φ : ((i : Fin n) → CMatrix (p i)) →⋆ₐ[ℂ] CMatrix m)
    (hφ : ∀ X Y, φ X = φ Y ↔ ∀ i, keep i → X i = Y i)
    (hp : ∀ i, keep i → 0 < p i)

theorem matrixRetainedBlockRangeBlocks_symm_single
    (i : Fin (Fintype.card {i : Fin n // keep i}))
    (X : CMatrix (p (matrixRetainedBlockLabel keep i))) :
    (matrixRetainedBlockRangeBlocks p keep φ hφ hp).equiv.symm (Pi.single i X) =
      φ.rangeRestrict (Pi.single (matrixRetainedBlockLabel keep i) X) := by
  classical
  apply (matrixRetainedBlockRangeBlocks p keep φ hφ hp).equiv.injective
  change (matrixRetainedBlockRangeBlocks p keep φ hφ hp).equiv
      ((matrixRetainedBlockRangeBlocks p keep φ hφ hp).equiv.symm (Pi.single i X)) =
    (matrixRetainedBlockRangeBlocks p keep φ hφ hp).equiv
      (φ.rangeRestrict (Pi.single (matrixRetainedBlockLabel keep i) X))
  rw [StarAlgEquiv.apply_symm_apply]
  funext j
  rw [matrixRetainedBlockRangeBlocks_equiv_map]
  by_cases hji : j = i
  · subst j
    simp only [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hji, Pi.single_eq_of_ne
      (fun h => hji (matrixRetainedBlockLabel_injective keep h))]

theorem matrixRetainedBlockRangeBlocks_unit
    (i : Fin (Fintype.card {i : Fin n // keep i}))
    (a b : Fin (p (matrixRetainedBlockLabel keep i))) :
    (matrixStarBlockUnit φ.range (matrixRetainedBlockRangeBlocks p keep φ hφ hp) i a b : CMatrix m) =
      φ (Pi.single (matrixRetainedBlockLabel keep i) (Matrix.single a b 1)) := by
  change ((matrixRetainedBlockRangeBlocks p keep φ hφ hp).equiv.symm
    (Pi.single i (Matrix.single a b 1)) : CMatrix m) = _
  rw [matrixRetainedBlockRangeBlocks_symm_single]
  rfl

theorem matrixRetainedBlockRangeBlocks_support
    (i : Fin (Fintype.card {i : Fin n // keep i})) :
    matrixStarBlockSupport φ.range (matrixRetainedBlockRangeBlocks p keep φ hφ hp) i =
      φ (Pi.single (matrixRetainedBlockLabel keep i) 1) := by
  rw [matrixStarBlockSupport_diagonal_sum]
  change (∑ a, (matrixStarBlockUnit _ (matrixRetainedBlockRangeBlocks p keep φ hφ hp) i a a : CMatrix m)) = _
  simp only [matrixRetainedBlockRangeBlocks_unit]
  rw [← map_sum]
  apply congrArg φ
  funext j
  by_cases hji : j = matrixRetainedBlockLabel keep i
  · subst j
    simp only [Finset.sum_apply, Pi.single_eq_same, Matrix.sum_single_one]
  · simp only [Finset.sum_apply, Pi.single_eq_of_ne hji, Finset.sum_const_zero]

theorem matrixRetainedBlockRangeBlocks_scalar (c : Fin n → ℝ) :
    matrixStarBlockScalar φ.range (matrixRetainedBlockRangeBlocks p keep φ hφ hp)
      (fun i : Fin (Fintype.card {i : Fin n // keep i}) => c (matrixRetainedBlockLabel keep i)) =
      φ (fun i => (c i : ℂ) • (1 : CMatrix (p i))) := by
  have he : matrixStarBlockScalarElement φ.range (matrixRetainedBlockRangeBlocks p keep φ hφ hp)
      (fun i : Fin (Fintype.card {i : Fin n // keep i}) => c (matrixRetainedBlockLabel keep i)) =
      φ.rangeRestrict (fun i => (c i : ℂ) • (1 : CMatrix (p i))) := by
    apply (matrixRetainedBlockRangeBlocks p keep φ hφ hp).equiv.injective
    change (matrixRetainedBlockRangeBlocks p keep φ hφ hp).equiv
        (matrixStarBlockScalarElement φ.range (matrixRetainedBlockRangeBlocks p keep φ hφ hp)
          (fun i : Fin (Fintype.card {i : Fin n // keep i}) => c (matrixRetainedBlockLabel keep i))) =
      (matrixRetainedBlockRangeBlocks p keep φ hφ hp).equiv
        (φ.rangeRestrict (fun i => (c i : ℂ) • (1 : CMatrix (p i))))
    funext i
    rw [matrixStarBlockScalarElement_equiv, matrixRetainedBlockRangeBlocks_equiv_map]
  exact congrArg Subtype.val he

end ThomGame.Analysis
