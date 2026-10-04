module

public import ThomGame.Groups.LaurentAlgebra
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# The concrete semidirect matrix group

We use GL₃ of the Laurent ring and GL₃(Z). The assigned generators are
elementary matrices and integral shears, as in the paper. Proving the
separation only needs a homomorphism to this ambient group, not surjectivity.
-/

@[expose] public noncomputable section
namespace ThomGame.LaurentModel

open Compressor ElementaryMatrix

abbrev LaurentMatrixGroup := Matrix.GeneralLinearGroup Axis Laurent

def matrixAction (A : IntegralGroup) : MulAut LaurentMatrixGroup :=
  Units.mapEquiv (ringAction A).mapMatrix.toMulEquiv

theorem matrixAction_apply (A : IntegralGroup) (M : LaurentMatrixGroup) (i j : Axis) :
    (matrixAction A M : Matrix Axis Axis Laurent) i j = ringAction A (M i j) := rfl

def semidirectAction : IntegralGroup →* MulAut LaurentMatrixGroup where
  toFun := matrixAction
  map_one' := by
    apply MulEquiv.ext
    intro M
    apply Units.ext
    apply Matrix.ext
    intro i j
    exact ringAction_one (M i j)
  map_mul' A B := by
    apply MulEquiv.ext
    intro M
    apply Units.ext
    apply Matrix.ext
    intro i j
    exact ringAction_mul A B (M i j)

abbrev ModelGroup := LaurentMatrixGroup ⋊[semidirectAction] IntegralGroup

def elementaryHom : LaurentMatrixGroup →* ModelGroup := SemidirectProduct.inl
def integralHom : IntegralGroup →* ModelGroup := SemidirectProduct.inr

def matrixX (r : Root) (p : Laurent) : ModelGroup := elementaryHom (elem r p)
def matrixS (s : Root) : ModelGroup := integralHom (integralShear s)

def generatorImage : Generator → ModelGroup
  | .inl (r, m) => matrixX r (coefficient m)
  | .inr s => matrixS s

theorem matrixX_fifth (r : Root) (p : Laurent) : matrixX r p ^ 5 = 1 := by
  rw [matrixX, ← map_pow, elem_pow, five_nsmul, elem_zero, map_one]

theorem matrixX_commute (r s : Root) (hrs : separated r s) (p q : Laurent) :
    Commute (matrixX r p) (matrixX s q) := (elem_commute r s hrs p q).map elementaryHom

theorem matrixX_commutator (r : Root) (p q : Laurent) :
    matrixX r p * matrixX (right r) q * (matrixX r p)⁻¹ * (matrixX (right r) q)⁻¹ =
      matrixX (across r) (p * q) := by
  simp only [matrixX, ← map_inv, ← map_mul, elem_commutator]

theorem matrixX_commutator_across (r : Root) (p q : Laurent) :
    matrixX (across r) p * matrixX (reverse (right r)) q *
      (matrixX (across r) p)⁻¹ * (matrixX (reverse (right r)) q)⁻¹ = matrixX r (p * q) := by
  simp only [matrixX, ← map_inv, ← map_mul, elem_commutator_across]

theorem matrixS_commute (r s : Root) (hrs : separated r s) :
    Commute (matrixS r) (matrixS s) := (integralShear_commute r s hrs).map integralHom

theorem matrixS_commutator (r : Root) :
    matrixS r * matrixS (right r) * (matrixS r)⁻¹ * (matrixS (right r))⁻¹ = matrixS (across r) := by
  simp only [matrixS, ← map_inv, ← map_mul, integralShear_commutator]

theorem matrixS_torsion :
    (matrixS root12 * (matrixS (reverse root12))⁻¹ * matrixS root12) ^ 4 = 1 := by
  simp only [matrixS, ← map_inv, ← map_mul, ← map_pow, integralShear_torsion, map_one]

theorem integral_conjugate_matrixX (A : IntegralGroup) (r : Root) (p : Laurent) :
    integralHom A * matrixX r p * (integralHom A)⁻¹ = matrixX r (ringAction A p) := by
  change SemidirectProduct.inr A * SemidirectProduct.inl (elem r p) *
      (SemidirectProduct.inr A)⁻¹ = SemidirectProduct.inl (elem r (ringAction A p))
  rw [← map_inv, ← SemidirectProduct.inl_aut]
  apply congrArg SemidirectProduct.inl
  exact map_elem (ringAction A).toRingHom r p

end ThomGame.LaurentModel
