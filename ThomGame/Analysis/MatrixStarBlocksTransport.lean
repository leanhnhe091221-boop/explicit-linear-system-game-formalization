module

public import ThomGame.Analysis.MatrixStarBlockScalarCoordinates
public import ThomGame.Analysis.MatrixSubalgebraScale

/-!
# Block labels transported by an actual trace-preserving star equivalence

The same labels, matrix sizes and scalar coordinates are retained.
Preservation of the unnormalized trace identifies the actual ranks.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped Matrix.Norms.L2Operator

variable {d m : Nat} (A : StarSubalgebra ℂ (CMatrix d)) (B : StarSubalgebra ℂ (CMatrix m))
    (P : MatrixSubalgebraStarBlocks A) (e : B ≃⋆ₐ[ℂ] A)

noncomputable abbrev matrixStarBlocksTransport : MatrixSubalgebraStarBlocks B where
  count := P.count
  size := P.size
  size_pos := P.size_pos
  equiv := e.trans P.equiv

theorem matrixStarBlocksTransport_unit (i : Fin P.count) (a b : Fin (P.size i)) :
    e (matrixStarBlockUnit B (matrixStarBlocksTransport A B P e) i a b) = matrixStarBlockUnit A P i a b := by
  change e (e.symm (P.equiv.symm (Pi.single i (Matrix.single a b 1)))) = _
  exact e.apply_symm_apply _

theorem matrixStarBlocksTransport_scalar (c : Fin P.count → ℝ) :
    e (matrixStarBlockScalarElement B (matrixStarBlocksTransport A B P e) c) =
      matrixStarBlockScalarElement A P c := by
  apply P.equiv.injective
  change P.equiv (e (matrixStarBlockScalarElement B (matrixStarBlocksTransport A B P e) c)) =
    P.equiv (matrixStarBlockScalarElement A P c)
  funext i
  change (matrixStarBlocksTransport A B P e).equiv
    (matrixStarBlockScalarElement B (matrixStarBlocksTransport A B P e) c) i = _
  rw [matrixStarBlockScalarElement_equiv, matrixStarBlockScalarElement_equiv]

theorem matrixStarBlocksTransport_multiplicity
    (htrace : ∀ X : B, Matrix.trace (X : CMatrix m) = Matrix.trace (e X : CMatrix d)) (i : Fin P.count) :
    matrixStarRepresentationMultiplicity B (matrixStarBlocksTransport A B P e) B.subtype i =
      matrixStarRepresentationMultiplicity A P A.subtype i := by
  let a : Fin (P.size i) := ⟨0, P.size_pos i⟩
  have hX := matrixStarRepresentationUnit_diagonal_projection B (matrixStarBlocksTransport A B P e) B.subtype i a
  have hY := matrixStarRepresentationUnit_diagonal_projection A P A.subtype i a
  have ht := htrace (matrixStarBlockUnit B (matrixStarBlocksTransport A B P e) i a a)
  rw [matrixStarBlocksTransport_unit] at ht
  exact matrixIdempotent_rank_eq_of_trace_eq hX.isIdempotentElem hY.isIdempotentElem ht

theorem matrixStarBlocksTransport_scale
    (htrace : ∀ X : B, Matrix.trace (X : CMatrix m) = Matrix.trace (e X : CMatrix d)) :
    (e ⟨matrixSubalgebraScale B (matrixStarBlocksTransport A B P e),
      matrixSubalgebraScale_mem B (matrixStarBlocksTransport A B P e)⟩ : CMatrix d) =
      matrixSubalgebraScale A P := by
  have h := matrixStarBlocksTransport_scalar A B P e
    (fun i => (P.size i : ℝ) / matrixStarRepresentationMultiplicity A P A.subtype i)
  have hm : (fun i => (P.size i : ℝ) /
      matrixStarRepresentationMultiplicity B (matrixStarBlocksTransport A B P e) B.subtype i) =
      fun i => (P.size i : ℝ) / matrixStarRepresentationMultiplicity A P A.subtype i := by
    funext i
    rw [matrixStarBlocksTransport_multiplicity A B P e htrace i]
  change (e (matrixStarBlockScalarElement B (matrixStarBlocksTransport A B P e)
    (fun i => (P.size i : ℝ) /
      matrixStarRepresentationMultiplicity B (matrixStarBlocksTransport A B P e) B.subtype i)) : CMatrix d) = _
  rw [hm]
  exact congrArg Subtype.val h

end ThomGame.Analysis
