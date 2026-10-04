module

public import ThomGame.Analysis.MatrixAlgebraicRepresentationTrace
public import ThomGame.Analysis.MatrixStarBlockUnits

/-!
# The actual Bratteli multiplicities of an inclusion

Restrict each target simple-block representation to the source algebra.
The rank multiplicities give both dimension equations of the inclusion.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {d : Nat} (B C : StarSubalgebra ℂ (CMatrix d))
    (P : MatrixSubalgebraStarBlocks B) (Q : MatrixSubalgebraStarBlocks C) (hBC : B ≤ C)

noncomputable def matrixInclusionBlockRepresentation (j : Fin Q.count) : B →⋆ₐ[ℂ] CMatrix (Q.size j) :=
  (Pi.evalStarAlgHom ℂ (fun j => CMatrix (Q.size j)) j).comp
    (Q.equiv.toStarAlgHom.comp (StarSubalgebra.inclusion hBC))

theorem matrixInclusionBlockRepresentation_apply (j : Fin Q.count) (X : B) :
    matrixInclusionBlockRepresentation B C Q hBC j X = Q.equiv (StarSubalgebra.inclusion hBC X) j := rfl

noncomputable def matrixInclusionMultiplicity (j : Fin Q.count) (i : Fin P.count) : Nat :=
  matrixStarRepresentationMultiplicity B P (matrixInclusionBlockRepresentation B C Q hBC j) i

theorem matrixInclusionMultiplicity_row (j : Fin Q.count) :
    Q.size j = ∑ i, P.size i * matrixInclusionMultiplicity B C P Q hBC j i :=
  matrixStarRepresentation_dimension B P (matrixInclusionBlockRepresentation B C Q hBC j)

theorem matrixInclusionMultiplicity_column (i : Fin P.count) :
    matrixStarRepresentationMultiplicity B P B.subtype i =
      ∑ j, matrixStarRepresentationMultiplicity C Q C.subtype j * matrixInclusionMultiplicity B C P Q hBC j i := by
  let a : Fin (P.size i) := ⟨0, P.size_pos i⟩
  let X : C := StarSubalgebra.inclusion hBC (matrixStarBlockUnit B P i a a)
  have hX : IsIdempotentElem X := by
    change X * X = X
    dsimp only [X]
    rw [← map_mul, matrixAlgebraicBlockUnit_mul_same]
  exact matrixAlgebraicRepresentation_idempotent_rank C Q.toAlgebraic C.subtype.toAlgHom X hX

theorem matrixInclusionMultiplicity_size_bound (j : Fin Q.count) (i : Fin P.count) :
    P.size i * matrixInclusionMultiplicity B C P Q hBC j i ≤ Q.size j := by
  rw [matrixInclusionMultiplicity_row B C P Q hBC j]
  exact Finset.single_le_sum (f := fun i => P.size i * matrixInclusionMultiplicity B C P Q hBC j i)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

theorem matrixInclusionMultiplicity_multiplicity_bound (j : Fin Q.count) (i : Fin P.count) :
    matrixStarRepresentationMultiplicity C Q C.subtype j * matrixInclusionMultiplicity B C P Q hBC j i ≤
      matrixStarRepresentationMultiplicity B P B.subtype i := by
  rw [matrixInclusionMultiplicity_column B C P Q hBC i]
  exact Finset.single_le_sum (f := fun j => matrixStarRepresentationMultiplicity C Q C.subtype j *
    matrixInclusionMultiplicity B C P Q hBC j i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

end ThomGame.Analysis
