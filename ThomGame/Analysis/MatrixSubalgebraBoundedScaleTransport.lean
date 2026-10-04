module

public import ThomGame.Analysis.MatrixBoundedScaleTransport

/-!
# Bounded scales in matrix subalgebras and their representations

Membership and invertibility are explicit. Mapping the polynomial
identity X(T+S)=T suffices; no ambient extension of the representation
or unproved inverse-closure property is used.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

theorem matrixBoundedScale_inclusion_norm {d : Nat}
    (D A : StarSubalgebra ℂ (CMatrix d))
    (P : MatrixSubalgebraStarBlocks D) (Q : MatrixSubalgebraStarBlocks A) (hDA : D ≤ A)
    (a : Fin Q.count → ℝ) (s : Fin P.count → ℝ)
    (ha : ∀ i, 0 < a i) (hs : ∀ i, 0 < s i) :
    matrixOpNorm (matrixBoundedScale (matrixStarBlockScalar A Q a) (matrixStarBlockScalar D P s)) ≤ 1 := by
  have hx := Matrix.nonneg_iff_posSemidef.mpr
    (matrixBoundedScale_inclusion_posDef D A P Q hDA a s ha hs).posSemidef
  have hy := Matrix.nonneg_iff_posSemidef.mpr
    (matrixBoundedScale_inclusion_one_sub_posDef D A P Q hDA a s ha hs).posSemidef
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ hx).mpr (sub_nonneg.mp hy)

theorem matrixSubalgebraBoundedScale_map {d m : Nat}
    (A : StarSubalgebra ℂ (CMatrix d)) (ρ : A →⋆ₐ[ℂ] CMatrix m) (T S X : A)
    (hX : (X : CMatrix d) = matrixBoundedScale (T : CMatrix d) (S : CMatrix d))
    (hTS : IsUnit ((T : CMatrix d) + S)) (hρTS : IsUnit (ρ T + ρ S)) :
    ρ X = matrixBoundedScale (ρ T) (ρ S) := by
  have hm : X * (T + S) = T := by
    apply Subtype.ext
    change (X : CMatrix d) * ((T : CMatrix d) + S) = T
    rw [hX, matrixBoundedScale, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hTS), Matrix.mul_one]
  have he := congrArg ρ hm
  simp only [map_mul, map_add] at he
  have hi : (ρ T + ρ S) * (ρ T + ρ S)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hρTS)
  calc
    ρ X = ρ X * ((ρ T + ρ S) * (ρ T + ρ S)⁻¹) := by rw [hi, Matrix.mul_one]
    _ = matrixBoundedScale (ρ T) (ρ S) := by rw [← Matrix.mul_assoc, he]; rfl

end ThomGame.Analysis
