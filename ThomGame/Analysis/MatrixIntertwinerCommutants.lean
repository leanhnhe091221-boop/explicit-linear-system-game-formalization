module

public import ThomGame.Analysis.MatrixBicommutant
public import ThomGame.Analysis.MatrixThomExactIntertwinerSupports

/-!
# Transporting commutants through actual rectangular star intertwiners

An intertwiner for A' transports A into the commutant of the target
representation. Its adjoint transports that commutant back into A,
using the proved finite matrix bicommutant theorem.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d m : Nat} {B : StarSubalgebra ℂ (CMatrix d)}

theorem matrixRepresentationIntertwiner_adjoint (ρ : B →⋆ₐ[ℂ] CMatrix m)
    (W : Matrix (Fin m) (Fin d) ℂ) (hW : ∀ b : B, ρ b * W = W * (b : CMatrix d)) (b : B) :
    Wᴴ * ρ b = (b : CMatrix d) * Wᴴ := by
  have he := hW (star b)
  change ρ (star b) * W = W * star (b : CMatrix d) at he
  rw [map_star] at he
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose] using congrArg Matrix.conjTranspose he

variable [NeZero d] (A : StarSubalgebra ℂ (CMatrix d))
    (ρ : StarSubalgebra.centralizer ℂ (A : Set (CMatrix d)) →⋆ₐ[ℂ] CMatrix m)
    (W : Matrix (Fin m) (Fin d) ℂ)
    (hW : ∀ a : StarSubalgebra.centralizer ℂ (A : Set (CMatrix d)), ρ a * W = W * (a : CMatrix d))

include hW

theorem matrixCommutantIntertwiner_initial_mem : Wᴴ * W ∈ A :=
  matrixSubalgebra_mem_of_bicommutant A _ (matrixRepresentationIntertwiner_gram_commutants ρ W hW).1

omit [NeZero d] in
theorem matrixCommutantIntertwiner_final_mem :
    W * Wᴴ ∈ StarSubalgebra.centralizer ℂ (ρ.range : Set (CMatrix m)) :=
  (matrixRepresentationIntertwiner_gram_commutants ρ W hW).2

omit [NeZero d] in
theorem matrixCommutantIntertwiner_push_mem (X : CMatrix d) (hX : X ∈ A) :
    W * X * Wᴴ ∈ StarSubalgebra.centralizer ℂ (ρ.range : Set (CMatrix m)) := by
  apply (mem_matrixSubalgebraCommutant_iff ρ.range _).mpr
  intro Y hY
  have hy : ∃ a, ρ a = Y := hY
  obtain ⟨a, rfl⟩ := hy
  have ha : (a : CMatrix d) * X = X * (a : CMatrix d) :=
    ((mem_matrixSubalgebraCommutant_iff A a).mp a.property X hX).symm
  calc
    ρ a * (W * X * Wᴴ) = (ρ a * W) * X * Wᴴ := by simp only [Matrix.mul_assoc]
    _ = W * ((a : CMatrix d) * X) * Wᴴ := by rw [hW]; simp only [Matrix.mul_assoc]
    _ = W * X * ((a : CMatrix d) * Wᴴ) := by rw [ha]; simp only [Matrix.mul_assoc]
    _ = (W * X * Wᴴ) * ρ a := by rw [← matrixRepresentationIntertwiner_adjoint ρ W hW a]; simp only [Matrix.mul_assoc]

theorem matrixCommutantIntertwiner_pull_mem (Y : CMatrix m)
    (hY : Y ∈ StarSubalgebra.centralizer ℂ (ρ.range : Set (CMatrix m))) : Wᴴ * Y * W ∈ A := by
  apply matrixSubalgebra_mem_of_bicommutant A
  apply (mem_matrixSubalgebraCommutant_iff _ _).mpr
  intro a ha
  let a' : StarSubalgebra.centralizer ℂ (A : Set (CMatrix d)) := ⟨a, ha⟩
  have hc : ρ a' * Y = Y * ρ a' := (mem_matrixSubalgebraCommutant_iff ρ.range Y).mp hY _ ⟨a', rfl⟩
  calc
    a * (Wᴴ * Y * W) = (Wᴴ * ρ a') * Y * W := by
      rw [matrixRepresentationIntertwiner_adjoint ρ W hW a']
      simp only [a', Matrix.mul_assoc]
    _ = Wᴴ * (Y * ρ a') * W := by rw [Matrix.mul_assoc Wᴴ (ρ a') Y, hc]
    _ = Wᴴ * Y * (ρ a' * W) := by simp only [Matrix.mul_assoc]
    _ = (Wᴴ * Y * W) * a := by rw [hW]; simp only [a', Matrix.mul_assoc]

end ThomGame.Analysis
