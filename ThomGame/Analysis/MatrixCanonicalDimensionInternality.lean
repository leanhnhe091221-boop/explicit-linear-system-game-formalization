module

public import ThomGame.Analysis.MatrixCanonicalDimensionStability

/-!
# Internality is invariant under canonical dimension identification

The reverse direction constructs source-dimensional coordinates in the
same common ambient space. No algebra-dependent ambient equivalence is used.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix Filter
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} (source target : ι → Nat) [∀ i, NeZero (source i)]
    (ht : ∀ i, 0 < target i) (L : Filter ι)
    (hratio : Tendsto (fun i => (source i : ℝ) / target i) L (𝓝 1))

theorem exists_matrixCanonicalDimensionPreimage
    (B : (i : ι) → StarSubalgebra ℂ (CMatrix (target i))) :
    ∃ A : (i : ι) → StarSubalgebra ℂ (CMatrix (source i)),
      (matrixInternalQuotient source A L).map
        (matrixCanonicalDimensionEquiv source target (fun i => NeZero.pos (source i)) ht L hratio).toStarAlgHom =
        matrixInternalQuotient target B L := by
  let N : ι → Nat := fun i => max (source i) (target i)
  let hN : ∀ i, 0 < N i := fun i => (NeZero.pos (source i)).trans_le (Nat.le_max_left _ _)
  let : ∀ i, NeZero (N i) := fun i => ⟨Nat.ne_of_gt (hN i)⟩
  let C : (i : ι) → StarSubalgebra ℂ (CMatrix (N i)) :=
    fun i => matrixCanonicalTargetAlgebra (m := source i) (B i)
  have hrS := matrixDimensionRatio_max_source_tendsto source target (fun i => NeZero.pos (source i)) L hratio
  have hrT := matrixDimensionRatio_max_target_tendsto source target ht L hratio
  obtain ⟨A, hA⟩ := exists_matrixDimensionDecreasing_canonical_algebras N source
    (fun i => Nat.le_max_left _ _) C (fun i => NeZero.pos (source i)) hrS
  change (matrixInternalQuotient source A L).map
    (matrixCanonicalSourceToCommon source target (fun i => NeZero.pos (source i)) L hratio).toStarAlgHom =
    matrixInternalQuotient N C L at hA
  have hB : (matrixInternalQuotient target B L).map
      (matrixCanonicalTargetToCommon source target ht L hratio).toStarAlgHom =
      matrixInternalQuotient N C L :=
    matrixFrameQuotientHom_internal_map target N
      (fun i => matrixCanonicalCornerFrame (Nat.le_max_right (source i) (target i)))
      (fun i => matrixCanonicalCornerFrame_initial (Nat.le_max_right (source i) (target i)))
      ht hN L hrT B
  refine ⟨A, ?_⟩
  apply StarSubalgebra.map_injective (matrixCanonicalTargetToCommon source target ht L hratio).injective
  rw [StarSubalgebra.map_map]
  change (matrixInternalQuotient source A L).map
    ((matrixCanonicalTargetToCommon source target ht L hratio).toStarAlgHom.comp
      (matrixCanonicalDimensionEquiv source target (fun i => NeZero.pos (source i)) ht L hratio).toStarAlgHom) =
    (matrixInternalQuotient target B L).map
      (matrixCanonicalTargetToCommon source target ht L hratio).toStarAlgHom
  have hc : (matrixCanonicalTargetToCommon source target ht L hratio).toStarAlgHom.comp
      (matrixCanonicalDimensionEquiv source target (fun i => NeZero.pos (source i)) ht L hratio).toStarAlgHom =
      (matrixCanonicalSourceToCommon source target (fun i => NeZero.pos (source i)) L hratio).toStarAlgHom := by
    ext x
    exact matrixCanonicalDimensionEquiv_to_common source target (fun i => NeZero.pos (source i)) ht L hratio x
  rw [hc, hA, hB]

theorem matrixCanonicalDimension_internal_iff (D : StarSubalgebra ℂ (MatrixTracialQuotient source L)) :
    (∃ A : (i : ι) → StarSubalgebra ℂ (CMatrix (source i)), D = matrixInternalQuotient source A L) ↔
      ∃ B : (i : ι) → StarSubalgebra ℂ (CMatrix (target i)),
        D.map (matrixCanonicalDimensionEquiv source target (fun i => NeZero.pos (source i)) ht L hratio).toStarAlgHom =
          matrixInternalQuotient target B L := by
  constructor
  · rintro ⟨A, rfl⟩
    obtain ⟨B, he, _⟩ := exists_matrixCanonicalDimensionStability source target ht L hratio A
    exact ⟨B, he⟩
  · rintro ⟨B, hB⟩
    obtain ⟨A, hA⟩ := exists_matrixCanonicalDimensionPreimage source target ht L hratio B
    exact ⟨A, StarSubalgebra.map_injective
      (matrixCanonicalDimensionEquiv source target (fun i => NeZero.pos (source i)) ht L hratio).injective
      (hB.trans hA.symm)⟩

end ThomGame.Analysis
