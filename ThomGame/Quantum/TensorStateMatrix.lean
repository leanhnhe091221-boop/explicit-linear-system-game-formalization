module

public import ThomGame.Quantum.FiniteStrategy
public import ThomGame.Analysis.RectangularHilbertSchmidt
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-! Coefficients of the actual bipartite state, with Bob indexing rows and Alice columns. -/

@[expose] public section
namespace ThomGame.Quantum

open Analysis Matrix
open scoped TensorProduct BigOperators

noncomputable def localMatrix {d : Nat} (A : LocalSpace d →L[ℂ] LocalSpace d) : CMatrix d :=
  LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun (Fin d) ℂ) A.toLinearMap

theorem localMatrix_apply {d : Nat} (A : LocalSpace d →L[ℂ] LocalSpace d) (i j : Fin d) :
    localMatrix A i j = A (EuclideanSpace.single j 1) i := by
  simp [localMatrix, LinearMap.toMatrixOrthonormal_apply_apply,
    EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]

theorem localMatrix_mul {d : Nat} (A B : LocalSpace d →L[ℂ] LocalSpace d) :
    localMatrix (A * B) = localMatrix A * localMatrix B := by
  exact map_mul (LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun (Fin d) ℂ)) _ _

theorem localMatrix_one (d : Nat) : localMatrix (1 : LocalSpace d →L[ℂ] LocalSpace d) = 1 :=
  map_one (LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun (Fin d) ℂ))

theorem localMatrix_sub {d : Nat} (A B : LocalSpace d →L[ℂ] LocalSpace d) :
    localMatrix (A - B) = localMatrix A - localMatrix B :=
  map_sub (LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun (Fin d) ℂ)) _ _

theorem localMatrix_smul {d : Nat} (z : ℂ) (A : LocalSpace d →L[ℂ] LocalSpace d) :
    localMatrix (z • A) = z • localMatrix A :=
  map_smul (LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun (Fin d) ℂ)) z _

theorem localMatrix_star {d : Nat} (A : LocalSpace d →L[ℂ] LocalSpace d) :
    localMatrix (star A) = (localMatrix A)ᴴ := by
  change LinearMap.toMatrixOrthonormal _ A.adjoint.toLinearMap = _
  rw [← ContinuousLinearMap.adjoint_toLinearMap]
  exact map_star (LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun (Fin d) ℂ)) _

theorem localMatrix_isHermitian {d : Nat} (A : LocalSpace d →L[ℂ] LocalSpace d)
    (hs : IsSelfAdjoint A) : Matrix.IsHermitian (localMatrix A) := by
  change (localMatrix A)ᴴ = localMatrix A
  rw [← localMatrix_star, hs.star_eq]

noncomputable def localMatrixUnitary {d : Nat} (A : LocalSpace d →L[ℂ] LocalSpace d)
    (hs : IsSelfAdjoint A) (hq : A * A = 1) : UnitaryMatrix d := by
  refine ⟨localMatrix A, ?_⟩
  change (localMatrix A)ᴴ * localMatrix A = 1 ∧ localMatrix A * (localMatrix A)ᴴ = 1
  rw [(localMatrix_isHermitian A hs).eq]
  have h : localMatrix A * localMatrix A = 1 := by rw [← localMatrix_mul, hq, localMatrix_one]
  exact ⟨h, h⟩

theorem localMatrix_apply_vector {d : Nat} (A : LocalSpace d →L[ℂ] LocalSpace d)
    (ξ : LocalSpace d) (i : Fin d) :
    (A ξ) i = ∑ j, localMatrix A i j * ξ j := by
  have h := congrFun (LinearMap.toMatrix_mulVec_repr
    (EuclideanSpace.basisFun (Fin d) ℂ).toBasis
    (EuclideanSpace.basisFun (Fin d) ℂ).toBasis A.toLinearMap ξ) i
  exact h.symm

noncomputable def tensorStateMatrix (d e : Nat) :
    BipartiteSpace d e →ₗ[ℂ] Matrix (Fin e) (Fin d) ℂ where
  toFun ψ j i := ((EuclideanSpace.basisFun (Fin d) ℂ).tensorProduct
    (EuclideanSpace.basisFun (Fin e) ℂ)).repr ψ (i, j)
  map_add' ξ ζ := by ext j i; simp; rfl
  map_smul' z ξ := by ext j i; simp; rfl

theorem tensorStateMatrix_tmul {d e : Nat} (ξ : LocalSpace d) (ζ : LocalSpace e)
    (j : Fin e) (i : Fin d) : tensorStateMatrix d e (ξ ⊗ₜ[ℂ] ζ) j i = ζ j * ξ i := by
  exact OrthonormalBasis.tensorProduct_repr_tmul_apply _ _ ξ ζ i j

theorem tensorStateMatrix_norm {d e : Nat} (ψ : BipartiteSpace d e) :
    rectHSNorm 1 (tensorStateMatrix d e ψ) = ‖ψ‖ := by
  let b := (EuclideanSpace.basisFun (Fin d) ℂ).tensorProduct (EuclideanSpace.basisFun (Fin e) ℂ)
  have h := EuclideanSpace.norm_sq_eq (b.repr ψ)
  rw [b.repr.norm_map, Fintype.sum_prod_type] at h
  have he : rectHSNorm 1 (tensorStateMatrix d e ψ) ^ 2 = ‖ψ‖ ^ 2 := by
    rw [rectHSNorm_sq, Nat.cast_one, div_one, h, Finset.sum_comm]
    rfl
  exact (sq_eq_sq₀ (rectHSNorm_nonneg _ _) (norm_nonneg _)).mp he

theorem tensorStateMatrix_bob {d e : Nat} (B : LocalSpace e →L[ℂ] LocalSpace e)
    (ψ : BipartiteSpace d e) :
    tensorStateMatrix d e (B.lTensor (LocalSpace d) ψ) = localMatrix B * tensorStateMatrix d e ψ := by
  induction ψ using TensorProduct.inductionOn with
  | tmul ξ ζ =>
    ext j i
    simp only [ContinuousLinearMap.lTensor_tmul, tensorStateMatrix_tmul, Matrix.mul_apply]
    rw [localMatrix_apply_vector, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  | add ξ ζ hξ hζ => simp only [map_add, hξ, hζ, Matrix.mul_add]

theorem tensorStateMatrix_alice {d e : Nat} (A : LocalSpace d →L[ℂ] LocalSpace d)
    (ψ : BipartiteSpace d e) :
    tensorStateMatrix d e (A.rTensor (LocalSpace e) ψ) = tensorStateMatrix d e ψ * (localMatrix A)ᵀ := by
  induction ψ using TensorProduct.inductionOn with
  | tmul ξ ζ =>
    ext j i
    simp only [ContinuousLinearMap.rTensor_tmul, tensorStateMatrix_tmul,
      Matrix.mul_apply, Matrix.transpose_apply]
    rw [localMatrix_apply_vector, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  | add ξ ζ hξ hζ => simp only [map_add, hξ, hζ, Matrix.add_mul]

theorem tensorStateMatrix_consistency_norm {d e : Nat}
    (A : LocalSpace d →L[ℂ] LocalSpace d) (B : LocalSpace e →L[ℂ] LocalSpace e)
    (ψ : BipartiteSpace d e) :
    rectHSNorm 1 (localMatrix B * tensorStateMatrix d e ψ -
      tensorStateMatrix d e ψ * (localMatrix A)ᵀ) =
        ‖B.lTensor (LocalSpace d) ψ - A.rTensor (LocalSpace e) ψ‖ := by
  rw [← tensorStateMatrix_bob, ← tensorStateMatrix_alice, ← map_sub, tensorStateMatrix_norm]

theorem tensorStateMatrix_bob_norm {d e : Nat}
    (B : LocalSpace e →L[ℂ] LocalSpace e) (ψ : BipartiteSpace d e) :
    rectHSNorm 1 (localMatrix B * tensorStateMatrix d e ψ) = ‖B.lTensor (LocalSpace d) ψ‖ := by
  rw [← tensorStateMatrix_bob, tensorStateMatrix_norm]

theorem tensorStateMatrix_bob_sub_smul_norm {d e : Nat}
    (B : LocalSpace e →L[ℂ] LocalSpace e) (z : ℂ) (ψ : BipartiteSpace d e) :
    rectHSNorm 1 (localMatrix B * tensorStateMatrix d e ψ - z • tensorStateMatrix d e ψ) =
      ‖B.lTensor (LocalSpace d) ψ - z • ψ‖ := by
  rw [← tensorStateMatrix_bob, ← map_smul, ← map_sub, tensorStateMatrix_norm]

end ThomGame.Quantum
