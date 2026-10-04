module

public import ThomGame.Analysis.MatrixCommutingDilation
public import ThomGame.Analysis.MatrixStinespringIntertwining

/-!
# The actual relative Stinespring data for Thom's correction

The same finite isometry realizes E_A, intertwines A and A' exactly,
and has the required uniform normalized error on every nearly included B.
The two factor representations commute on the entire dilation space.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat} {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
theorem matrixStinespring_range_projection (V : Matrix κ (Fin d) ℂ)
    (hV : Vᴴ * V = 1) : IsStarProjection (V * Vᴴ) := by
  constructor
  · change (V * Vᴴ) * (V * Vᴴ) = V * Vᴴ
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ V Vᴴ, hV, Matrix.one_mul]
  · change (V * Vᴴ)ᴴ = V * Vᴴ
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

theorem matrixStinespring_range_commutes
    (ρ : CMatrix d →⋆ₐ[ℂ] Matrix κ κ ℂ) (V : Matrix κ (Fin d) ℂ) (X : CMatrix d)
    (hX : ρ X * V = V * X) (hXs : ρ (star X) * V = V * star X) :
    (V * Vᴴ) * ρ X = ρ X * (V * Vᴴ) := by
  rw [map_star] at hXs
  have hs := congrArg Matrix.conjTranspose hXs
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose] at hs
  rw [Matrix.mul_assoc, hs, ← Matrix.mul_assoc, ← hX, Matrix.mul_assoc]

variable [NeZero d]

omit [DecidableEq κ] in
theorem matrixStinespring_range_trace (V : Matrix κ (Fin d) ℂ) (hV : Vᴴ * V = 1) :
    matrixTraceReal d (V * Vᴴ) = 1 := by
  rw [matrixTraceReal_mul_comm, hV]
  simp [matrixTraceReal, NeZero.ne d]

theorem exists_matrixRelativeStinespring (A : StarSubalgebra ℂ (CMatrix d)) :
    ∃ V : Matrix (Fin d × (Fin d × Fin d)) (Fin d) ℂ,
      Vᴴ * V = 1 ∧
      (∀ X, Vᴴ * matrixDiagonalRepresentation (Fin d × Fin d) d X * V = matrixTraceProjection A X) ∧
      (∀ X ∈ A, matrixDiagonalRepresentation (Fin d × Fin d) d X * V = V * X) ∧
      (∀ Y ∈ StarSubalgebra.centralizer ℂ (A : Set (CMatrix d)),
        matrixChoiRightRepresentation d Y * V = V * Y) ∧
      ∀ X, rectHSNorm d (matrixDiagonalRepresentation (Fin d × Fin d) d X * V - V * X) ^ 2 =
        2 * hsNorm (X - matrixTraceProjection A X) ^ 2 := by
  obtain ⟨S, hSA, hS⟩ := exists_matrixSubalgebra_choi_factor A (matrixConditionalExpectationCP A)
    (matrixTraceProjection_mem A)
  let V := matrixKrausColumn (matrixChoiKraus S)
  have hV : Vᴴ * V = 1 := by
    rw [matrixKrausColumn_inner]
    simpa only [matrixConditionalExpectationCP_apply, matrixTraceProjection_one, mul_one] using (hS 1).symm
  have hE (X : CMatrix d) :
      Vᴴ * matrixDiagonalRepresentation (Fin d × Fin d) d X * V = matrixTraceProjection A X :=
    (matrixKrausColumn_compression _ X).trans (hS X).symm
  exact ⟨V, hV, hE,
    matrixStinespring_expectation_intertwines A _ V hV hE,
    matrixChoiRightRepresentation_intertwines A S hSA,
    matrixStinespring_expectation_defect_sq A _ V hV hE⟩

theorem exists_matrixNearInclusion_relativeDilation
    (A B D : StarSubalgebra ℂ (CMatrix d)) (hDA : D ≤ A)
    {ε : ℝ} (hε : 0 ≤ ε) (hBA : MatrixNearInclusion B A ε) :
    ∃ V : Matrix (Fin d × (Fin d × Fin d)) (Fin d) ℂ,
      Vᴴ * V = 1 ∧
      (∀ X, Vᴴ * matrixDiagonalRepresentation (Fin d × Fin d) d X * V = matrixTraceProjection A X) ∧
      (∀ X ∈ D, matrixDiagonalRepresentation (Fin d × Fin d) d X * V = V * X) ∧
      (∀ Y ∈ StarSubalgebra.centralizer ℂ (A : Set (CMatrix d)),
        matrixChoiRightRepresentation d Y * V = V * Y ∧
        (V * Vᴴ) * matrixChoiRightRepresentation d Y = matrixChoiRightRepresentation d Y * (V * Vᴴ)) ∧
      IsStarProjection (V * Vᴴ) ∧ matrixTraceReal d (V * Vᴴ) = 1 ∧
      (∀ X ∈ B, matrixOpNorm X ≤ 1 →
        rectHSNorm d (matrixDiagonalRepresentation (Fin d × Fin d) d X * V - V * X) ≤ Real.sqrt 2 * ε) ∧
      ∀ X Y, Y ∈ StarSubalgebra.centralizer ℂ (A : Set (CMatrix d)) →
        Vᴴ * (matrixDiagonalRepresentation (Fin d × Fin d) d X * matrixChoiRightRepresentation d Y) * V =
          matrixTraceProjection A X * Y := by
  obtain ⟨V, hV, hE, hA, hC, _⟩ := exists_matrixRelativeStinespring A
  refine ⟨V, hV, hE, (fun X hX => hA X (hDA hX)), ?_,
    matrixStinespring_range_projection V hV, matrixStinespring_range_trace V hV,
    matrixStinespring_expectation_nearInclusion_bound A B hε hBA _ V hV hE, ?_⟩
  · intro Y hY
    exact ⟨hC Y hY, matrixStinespring_range_commutes _ V Y (hC Y hY)
      (hC (star Y) ((StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))).star_mem' hY))⟩
  · intro X Y hY
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hC Y hY, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, hE]

end ThomGame.Analysis
