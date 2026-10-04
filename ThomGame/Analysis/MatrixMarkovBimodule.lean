module

public import ThomGame.Analysis.MatrixMarkovPowers
public import ThomGame.Analysis.MatrixPartitionScalarAlgebra
public import ThomGame.Analysis.MatrixScalarGapPartition

/-!
# Bimodularity and trace self-adjointness of Markov powers

Every power is bimodular over the scalar diagonal algebra of an actual
reducing partition. Its adjoint for the normalized trace pairing is itself.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {d h : Nat}

theorem matrixUnitaryConjugation_bimodule (U : UnitaryMatrix d) (A X B : CMatrix d)
    (hA : Commute U.val A) (hB : Commute U.val B) :
    matrixUnitaryConjugation U (A * X * B) = A * matrixUnitaryConjugation U X * B := by
  rw [matrixUnitaryConjugation_mul, matrixUnitaryConjugation_mul,
    show matrixUnitaryConjugation U A = A from (commute_unitary_iff_star_right_conjugate U.prop).mp hA,
    show matrixUnitaryConjugation U B = B from (commute_unitary_iff_star_right_conjugate U.prop).mp hB]

theorem matrixUnitary_inv_commute (U : UnitaryMatrix d) {X : CMatrix d}
    (hX : Commute U.val X) : Commute (U⁻¹).val X := by
  apply (commute_unitary_iff_star_right_conjugate (U⁻¹).prop).mpr
  simpa only [Matrix.UnitaryGroup.inv_val, star_star] using
    (commute_unitary_iff_star_left_conjugate U.prop).mp hX

theorem matrixLazyMarkov_bimodule (U : Fin h → UnitaryMatrix d) (A X B : CMatrix d)
    (hA : ∀ j, Commute (U j).val A) (hB : ∀ j, Commute (U j).val B) :
    matrixLazyMarkov U (A * X * B) = A * matrixLazyMarkov U X * B := by
  simp only [matrixLazyMarkov_apply,
    fun j => matrixUnitaryConjugation_bimodule (U j) A X B (hA j) (hB j),
    fun j => matrixUnitaryConjugation_bimodule (U j)⁻¹ A X B
      (matrixUnitary_inv_commute (U j) (hA j)) (matrixUnitary_inv_commute (U j) (hB j)),
    mul_add, add_mul, mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]

theorem matrixLazyMarkov_pow_bimodule (U : Fin h → UnitaryMatrix d) (n : Nat) (A X B : CMatrix d)
    (hA : ∀ j, Commute (U j).val A) (hB : ∀ j, Commute (U j).val B) :
    (matrixLazyMarkov U ^ n) (A * X * B) = A * (matrixLazyMarkov U ^ n) X * B := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, matrixLazyMarkov_bimodule U A _ B hA hB,
        Module.End.mul_apply]

theorem matrixLazyMarkov_pow_pairing [NeZero d] (U : Fin h → UnitaryMatrix d) (n : Nat)
    (X Y : CMatrix d) :
    normalizedTrace (star ((matrixLazyMarkov U ^ n) X) * Y) =
      normalizedTrace (star X * (matrixLazyMarkov U ^ n) Y) := by
  induction n generalizing X Y with
  | zero => rfl
  | succ n ih =>
      calc
        _ = normalizedTrace (star (matrixLazyMarkov U ((matrixLazyMarkov U ^ n) X)) * Y) := by
          rw [pow_succ', Module.End.mul_apply]
        _ = normalizedTrace (star ((matrixLazyMarkov U ^ n) X) * matrixLazyMarkov U Y) :=
          matrixLazyMarkov_pairing U _ Y
        _ = normalizedTrace (star X * (matrixLazyMarkov U ^ n) (matrixLazyMarkov U Y)) := ih X _
        _ = _ := by rw [pow_succ, Module.End.mul_apply]

theorem MatrixScalarGapPartition.scalar_commute {U : Fin h → UnitaryMatrix d} {c : ℝ}
    (Q : MatrixScalarGapPartition U c) {A : CMatrix d}
    (hA : A ∈ matrixPartitionScalarAlgebra Q.E) (j : Fin h) : Commute (U j).val A := by
  have hU : (U j).val ∈ matrixPartitionBlockAlgebra Q.E :=
    (mem_matrixPartitionBlockAlgebra_iff Q.E Q.projection _).mpr (fun i => Q.reducing i j)
  exact (matrixPartitionScalarAlgebra_commute Q.E Q.projection Q.orthogonal Q.sum_one hU hA).symm

theorem MatrixScalarGapPartition.markov_pow_bimodule {U : Fin h → UnitaryMatrix d} {c : ℝ}
    (Q : MatrixScalarGapPartition U c) (n : Nat) (A X B : CMatrix d)
    (hA : A ∈ matrixPartitionScalarAlgebra Q.E) (hB : B ∈ matrixPartitionScalarAlgebra Q.E) :
    (matrixLazyMarkov U ^ n) (A * X * B) = A * (matrixLazyMarkov U ^ n) X * B :=
  matrixLazyMarkov_pow_bimodule U n A X B (Q.scalar_commute hA) (Q.scalar_commute hB)

end ThomGame.Analysis
