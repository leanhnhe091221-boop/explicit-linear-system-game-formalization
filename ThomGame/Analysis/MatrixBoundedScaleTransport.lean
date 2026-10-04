module

public import ThomGame.Analysis.MatrixBoundedScaleCells

/-!
# Exact transport of bounded scales

Both algebra homomorphisms and rectangular intertwiners preserve the
rational scale when the relevant sums are invertible.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d m : Nat}

theorem matrixNonsingular_inverse_intertwines (A : CMatrix m) (B : CMatrix d)
    (V : Matrix (Fin m) (Fin d) ℂ) (hA : IsUnit A) (hB : IsUnit B) (hAV : A * V = V * B) :
    A⁻¹ * V = V * B⁻¹ := by
  have hAi : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hA)
  have hBi : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hB)
  calc
    A⁻¹ * V = A⁻¹ * V * (B * B⁻¹) := by rw [hBi, Matrix.mul_one]
    _ = A⁻¹ * (V * B) * B⁻¹ := by simp only [Matrix.mul_assoc]
    _ = A⁻¹ * (A * V) * B⁻¹ := by rw [← hAV]
    _ = V * B⁻¹ := by rw [← Matrix.mul_assoc A⁻¹ A V, hAi, Matrix.one_mul]

theorem matrixBoundedScale_intertwines (T S : CMatrix m) (T' S' : CMatrix d)
    (V : Matrix (Fin m) (Fin d) ℂ) (hTS : IsUnit (T + S)) (hTS' : IsUnit (T' + S'))
    (hT : T * V = V * T') (hS : S * V = V * S') :
    matrixBoundedScale T S * V = V * matrixBoundedScale T' S' := by
  have he : (T + S) * V = V * (T' + S') := by rw [Matrix.add_mul, Matrix.mul_add, hT, hS]
  have hi := matrixNonsingular_inverse_intertwines (T + S) (T' + S') V hTS hTS' he
  rw [matrixBoundedScale, Matrix.mul_assoc, hi, ← Matrix.mul_assoc, hT, Matrix.mul_assoc]
  rfl

theorem matrixBoundedScale_intertwines_posDef (T S : CMatrix m) (T' S' : CMatrix d)
    (V : Matrix (Fin m) (Fin d) ℂ)
    (hTpos : T.PosDef) (hSpos : S.PosDef) (hTpos' : T'.PosDef) (hSpos' : S'.PosDef)
    (hT : T * V = V * T') (hS : S * V = V * S') :
    matrixBoundedScale T S * V = V * matrixBoundedScale T' S' :=
  matrixBoundedScale_intertwines T S T' S' V (hTpos.add hSpos).isUnit (hTpos'.add hSpos').isUnit hT hS

theorem matrixAlgHom_map_nonsing_inv (ρ : CMatrix d →ₐ[ℂ] CMatrix m) (X : CMatrix d) (hX : IsUnit X) :
    ρ X⁻¹ = (ρ X)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← map_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hX), map_one]

theorem matrixBoundedScale_map (ρ : CMatrix d →ₐ[ℂ] CMatrix m) (T S : CMatrix d) (hTS : IsUnit (T + S)) :
    ρ (matrixBoundedScale T S) = matrixBoundedScale (ρ T) (ρ S) := by
  rw [matrixBoundedScale, map_mul, matrixAlgHom_map_nonsing_inv ρ (T + S) hTS, map_add]
  rfl

end ThomGame.Analysis
