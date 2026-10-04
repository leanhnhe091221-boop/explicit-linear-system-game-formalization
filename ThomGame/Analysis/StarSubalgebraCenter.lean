module

public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.Basic.Complex.Basic

/-!
# The center of a star subalgebra, kept inside its original ambient algebra
-/

@[expose] public section
namespace ThomGame.Analysis

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]

def starSubalgebraCenter (A : StarSubalgebra ℂ R) : StarSubalgebra ℂ R :=
  A ⊓ StarSubalgebra.centralizer ℂ (A : Set R)

theorem mem_starSubalgebraCenter_iff (A : StarSubalgebra ℂ R) (x : R) :
    x ∈ starSubalgebraCenter A ↔ x ∈ A ∧ ∀ y ∈ A, y * x = x * y := by
  change (x ∈ A ∧ x ∈ StarSubalgebra.centralizer ℂ (A : Set R)) ↔ _
  rw [StarSubalgebra.mem_centralizer_iff]
  exact ⟨fun h => ⟨h.1, fun y hy => (h.2 y hy).1⟩,
    fun h => ⟨h.1, fun y hy => ⟨h.2 y hy, h.2 (star y) (A.star_mem' hy)⟩⟩⟩

theorem starSubalgebraCenter_le (A : StarSubalgebra ℂ R) : starSubalgebraCenter A ≤ A := inf_le_left

end ThomGame.Analysis
