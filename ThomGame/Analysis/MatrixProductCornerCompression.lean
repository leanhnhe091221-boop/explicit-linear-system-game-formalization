module

public import ThomGame.Analysis.MatrixReducingCompression
public import ThomGame.Analysis.MatrixRepresentationUnitBalls
public import ThomGame.Analysis.MatrixSubalgebraCornerUnitBalls
public import ThomGame.Analysis.MatrixStableCornerTransport

/-!
# Compression by a product of algebra and commutant projections

If P belongs to A and Q commutes with A, compression to PQ still has
an algebraic image. Restrict first to the elements of A commuting with P;
on that unital subalgebra the compression is a genuine star homomorphism.
Every compressed element of A has a preimage there, and every contraction
in the compressed algebra has a contraction preimage in A.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d k : Nat} (A : StarSubalgebra ℂ (CMatrix d))
    {P Q : CMatrix d} (hP : IsStarProjection P) (hPA : P ∈ A)
    (hQA : Q ∈ StarSubalgebra.centralizer ℂ (A : Set (CMatrix d)))
    (F : Matrix (Fin d) (Fin k) ℂ) (hFi : Fᴴ * F = 1) (hFf : F * Fᴴ = P * Q)

def matrixProjectionCommutingPart (P : CMatrix d) : StarSubalgebra ℂ (CMatrix d) :=
  A ⊓ StarSubalgebra.centralizer ℂ ({P} : Set (CMatrix d))

include hP in
theorem mem_matrixProjectionCommutingPart (X : CMatrix d) :
    X ∈ matrixProjectionCommutingPart A P ↔ X ∈ A ∧ P * X = X * P := by
  simp only [matrixProjectionCommutingPart, StarSubalgebra.mem_inf,
    StarSubalgebra.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq,
    hP.isSelfAdjoint.star_eq, and_self]

include hP hFi hFf in
theorem matrixProductCornerFrame_left_support : P * F = F := by
  calc
    P * F = P * (F * Fᴴ) * F := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hFi, Matrix.mul_one]
    _ = (P * P) * Q * F := by rw [hFf, ← Matrix.mul_assoc]
    _ = F := by rw [hP.isIdempotentElem.eq, ← hFf, Matrix.mul_assoc, hFi, Matrix.mul_one]

include hP hFi hFf in
theorem matrixProductCornerFrame_adjoint_support : Fᴴ * P = Fᴴ := by
  have he := congrArg Matrix.conjTranspose (matrixProductCornerFrame_left_support hP F hFi hFf)
  simpa only [Matrix.conjTranspose_mul, hP.isSelfAdjoint.isHermitian.eq] using he

include hP hQA hFf in
theorem matrixProductCornerFrame_reducing (X : CMatrix d) (hX : X ∈ matrixProjectionCommutingPart A P) :
    (F * Fᴴ) * X = X * (F * Fᴴ) := by
  obtain ⟨hXA, hXP⟩ := (mem_matrixProjectionCommutingPart A hP X).mp hX
  have hXQ := (mem_matrixSubalgebraCommutant_iff A Q).mp hQA X hXA
  rw [hFf, Matrix.mul_assoc, ← hXQ, ← Matrix.mul_assoc, hXP, Matrix.mul_assoc]

noncomputable def matrixProductCornerRepresentation :
    matrixProjectionCommutingPart A P →⋆ₐ[ℂ] CMatrix k :=
  matrixReducingRepresentation (matrixProjectionCommutingPart A P) (StarAlgHom.id ℂ (CMatrix d)) F hFi
    (matrixProductCornerFrame_reducing A hP hQA F hFf)

theorem matrixProductCornerRepresentation_apply (X : matrixProjectionCommutingPart A P) :
    matrixProductCornerRepresentation A hP hQA F hFi hFf X = Fᴴ * (X : CMatrix d) * F := rfl

include hPA in
theorem matrixProductCorner_compression_mem (X : CMatrix d) (hX : X ∈ A) :
    Fᴴ * X * F ∈ (matrixProductCornerRepresentation A hP hQA F hFi hFf).range := by
  have hY : P * X * P ∈ matrixProjectionCommutingPart A P := by
    apply (mem_matrixProjectionCommutingPart A hP _).mpr
    refine ⟨A.mul_mem (A.mul_mem hPA hX) hPA, ?_⟩
    calc
      P * (P * X * P) = (P * P) * X * P := by simp only [Matrix.mul_assoc]
      _ = P * X * P := by rw [hP.isIdempotentElem.eq]
      _ = P * X * P * P := by rw [Matrix.mul_assoc (P * X) P P, hP.isIdempotentElem.eq]
  refine ⟨⟨P * X * P, hY⟩, ?_⟩
  change Fᴴ * (P * X * P) * F = Fᴴ * X * F
  calc
    _ = (Fᴴ * P) * X * (P * F) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [matrixProductCornerFrame_left_support hP F hFi hFf,
      matrixProductCornerFrame_adjoint_support hP F hFi hFf]

theorem matrixProductCorner_contraction_lift (Y : CMatrix k)
    (hY : Y ∈ (matrixProductCornerRepresentation A hP hQA F hFi hFf).range)
    (hn : matrixOpNorm Y ≤ 1) :
    ∃ X ∈ A, matrixOpNorm X ≤ 1 ∧ Fᴴ * X * F = Y := by
  obtain ⟨X, hX, he⟩ := matrixStarRepresentation_contraction_lift _
    (matrixProductCornerRepresentation A hP hQA F hFi hFf) Y hY hn
  exact ⟨X, X.property.1, hX, he⟩

include hPA in
theorem matrixProductCorner_unitBall_compression_image :
    (fun X : CMatrix d => Fᴴ * X * F) '' {X : CMatrix d | X ∈ A ∧ matrixOpNorm X ≤ 1} =
      {Y : CMatrix k | Y ∈ (matrixProductCornerRepresentation A hP hQA F hFi hFf).range ∧ matrixOpNorm Y ≤ 1} := by
  ext Y
  constructor
  · rintro ⟨X, ⟨hX, hn⟩, rfl⟩
    exact ⟨matrixProductCorner_compression_mem A hP hPA hQA F hFi hFf X hX,
      (matrixFrameCompression_opNorm_le F hFi X).trans hn⟩
  · rintro ⟨hY, hn⟩
    obtain ⟨X, hX, hnX, he⟩ := matrixProductCorner_contraction_lift A hP hQA F hFi hFf Y hY hn
    exact ⟨X, ⟨hX, hnX⟩, he⟩

end ThomGame.Analysis
