module

public import ThomGame.Analysis.CStarArtinianSemisimple
public import ThomGame.Analysis.MatrixSubalgebraUnitaries
public import Mathlib.RingTheory.SimpleModule.IsAlgClosed
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Algebraic blocks of an actual finite matrix star subalgebra

The matrix subalgebra is proved semisimple from its C-star norm and finite
dimension. Wedderburn--Artin then constructs a product of full complex
matrix algebras. The equivalence here is algebraic: star compatibility,
unitary block realization and representation multiplicities are separate
steps, not fields assumed in this construction.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator

variable {d : Nat} (A : StarSubalgebra ℂ (CMatrix d))

instance matrixSubalgebraFiniteDimensional : FiniteDimensional ℂ A :=
  FiniteDimensional.of_injective A.subtype.toLinearMap Subtype.val_injective

theorem matrixSubalgebra_jacobson_eq_bot : Ring.jacobson A = ⊥ := by
  let : IsArtinianRing A := IsArtinianRing.of_finite ℂ A
  exact cstarArtinian_jacobson_eq_bot

theorem matrixSubalgebra_isSemisimpleRing : IsSemisimpleRing A := by
  let : IsArtinianRing A := IsArtinianRing.of_finite ℂ A
  exact cstarArtinian_isSemisimpleRing

theorem exists_matrixSubalgebra_algEquiv_pi_matrix :
    ∃ (n : Nat) (p : Fin n → Nat), (∀ i, NeZero (p i)) ∧
      Nonempty (A ≃ₐ[ℂ] ((i : Fin n) → CMatrix (p i))) := by
  let := matrixSubalgebra_isSemisimpleRing A
  exact IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ A

structure MatrixSubalgebraAlgebraicBlocks where
  count : Nat
  size : Fin count → Nat
  size_pos : ∀ i, 0 < size i
  equiv : A ≃ₐ[ℂ] ((i : Fin count) → CMatrix (size i))

theorem exists_matrixSubalgebraAlgebraicBlocks : Nonempty (MatrixSubalgebraAlgebraicBlocks A) := by
  obtain ⟨n, p, hp, ⟨e⟩⟩ := exists_matrixSubalgebra_algEquiv_pi_matrix A
  let := hp
  exact ⟨⟨n, p, fun i => NeZero.pos (p i), e⟩⟩

theorem matrixSubalgebraAlgebraicBlocks_finrank (S : MatrixSubalgebraAlgebraicBlocks A) :
    Module.finrank ℂ A = ∑ i, (S.size i) ^ 2 := by
  rw [S.equiv.toLinearEquiv.finrank_eq]
  simp [Module.finrank_pi_fintype, Module.finrank_matrix, pow_two]

theorem matrixSubalgebraAlgebraicBlocks_sum_sq_le (S : MatrixSubalgebraAlgebraicBlocks A) :
    ∑ i, (S.size i) ^ 2 ≤ d ^ 2 := by
  rw [← matrixSubalgebraAlgebraicBlocks_finrank A S]
  have h := LinearMap.finrank_le_finrank_of_injective
    (f := A.subtype.toLinearMap) Subtype.val_injective
  simpa [Module.finrank_matrix, pow_two] using h

end ThomGame.Analysis
