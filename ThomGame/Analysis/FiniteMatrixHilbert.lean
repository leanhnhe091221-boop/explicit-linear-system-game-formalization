module

public import ThomGame.Analysis.NormalizedTraceBounds
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# The normalized trace Hilbert space of a single matrix algebra

A separate type carries the normalized Hilbert--Schmidt norm. Its
linear equivalence with the actual matrix algebra fixes every entry.
-/

@[expose] public section
namespace ThomGame.Analysis

def FiniteMatrixHilbert (d : Nat) := CMatrix d

variable (d : Nat)

instance finiteMatrixHilbertAddCommGroup : AddCommGroup (FiniteMatrixHilbert d) :=
  inferInstanceAs (AddCommGroup (CMatrix d))

instance finiteMatrixHilbertModule : Module ℂ (FiniteMatrixHilbert d) :=
  inferInstanceAs (Module ℂ (CMatrix d))

def finiteMatrixHilbertEquiv : CMatrix d ≃ₗ[ℂ] FiniteMatrixHilbert d := LinearEquiv.refl ℂ _

instance finiteMatrixHilbertFiniteDimensional : FiniteDimensional ℂ (FiniteMatrixHilbert d) :=
  FiniteDimensional.of_injective (finiteMatrixHilbertEquiv d).symm.toLinearMap
    (finiteMatrixHilbertEquiv d).symm.injective

variable [NeZero d]

@[instance_reducible] noncomputable def finiteMatrixHilbertInnerCore : InnerProductSpace.Core ℂ (FiniteMatrixHilbert d) where
  inner x y := normalizedTrace (star ((finiteMatrixHilbertEquiv d).symm x) * (finiteMatrixHilbertEquiv d).symm y)
  conj_inner_symm x y := by
    change star (normalizedTrace _) = normalizedTrace _
    rw [← normalizedTrace_star, star_mul, star_star]
  re_inner_nonneg x := by
    rw [normalizedTrace_gram, RCLike.re_to_complex, Complex.ofReal_re]
    exact sq_nonneg _
  add_left x y z := by
    rw [map_add, star_add, add_mul, normalizedTrace_add]
  smul_left x y c := by
    rw [map_smul, star_smul, smul_mul_assoc, normalizedTrace_smul]
    rfl
  definite x hx := by
    apply (finiteMatrixHilbertEquiv d).symm.injective
    have hz : hsNorm ((finiteMatrixHilbertEquiv d).symm x) ^ 2 = 0 := by
      rw [normalizedTrace_gram, Complex.ofReal_eq_zero] at hx
      exact hx
    exact (hsNorm_eq_zero_iff _).mp (sq_eq_zero_iff.mp hz)

noncomputable instance finiteMatrixHilbertNormedAddCommGroup : NormedAddCommGroup (FiniteMatrixHilbert d) :=
  InnerProductSpace.Core.toNormedAddCommGroup (cd := finiteMatrixHilbertInnerCore d)

noncomputable instance finiteMatrixHilbertInnerProductSpace : InnerProductSpace ℂ (FiniteMatrixHilbert d) :=
  letI := finiteMatrixHilbertInnerCore d
  InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (FiniteMatrixHilbert d))

theorem finiteMatrixHilbert_inner (A B : CMatrix d) :
    inner ℂ (finiteMatrixHilbertEquiv d A) (finiteMatrixHilbertEquiv d B) = normalizedTrace (star A * B) := rfl

theorem finiteMatrixHilbert_norm (A : CMatrix d) : ‖finiteMatrixHilbertEquiv d A‖ = hsNorm A := by
  change Real.sqrt (normalizedTrace (star A * A)).re = hsNorm A
  rw [normalizedTrace_gram, Complex.ofReal_re, Real.sqrt_sq (hsNorm_nonneg _)]

end ThomGame.Analysis
