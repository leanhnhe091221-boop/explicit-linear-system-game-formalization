module

public import ThomGame.Groups.CompressorPresentation
public import Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations
public import Mathlib.Tactic.Abel

/-! Elementary matrices for the actual six roots of the compressor. -/

@[expose] public section
namespace ThomGame.ElementaryMatrix

open Compressor
variable {R : Type*} [CommRing R]

def elem (r : Root) (c : R) : Matrix.GeneralLinearGroup Axis R :=
  Matrix.GeneralLinearGroup.transvection (source r) (target r) r.property c

theorem coe_elem (r : Root) (c : R) :
    (elem r c : Matrix Axis Axis R) = 1 + Matrix.single (source r) (target r) c := rfl

theorem elem_inv (r : Root) (c : R) : (elem r c)⁻¹ = elem r (-c) := by
  apply Units.ext
  rfl

theorem elem_zero (r : Root) : elem r (0 : R) = 1 := by
  apply Units.ext
  simp [coe_elem]

theorem elem_add (r : Root) (a b : R) : elem r (a + b) = elem r a * elem r b := by
  apply Units.ext
  exact (Matrix.transvection_mul_transvection_same (i := source r) (j := target r) r.property a b).symm

theorem elem_pow (r : Root) (a : R) (n : Nat) : (elem r a) ^ n = elem r (n • a) := by
  induction n with
  | zero => simp [elem_zero]
  | succ n ih => rw [pow_succ, ih, succ_nsmul, elem_add]

theorem elem_commute (r s : Root) (hrs : separated r s) (a b : R) :
    Commute (elem r a) (elem s b) := by
  apply Units.ext
  change (1 + Matrix.single (source r) (target r) a) *
      (1 + Matrix.single (source s) (target s) b) =
    (1 + Matrix.single (source s) (target s) b) *
      (1 + Matrix.single (source r) (target r) a)
  simp [mul_add, add_mul, hrs.1.symm, hrs.2.symm]
  abel

theorem chain_commutator {i j k : Axis} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : R) :
    Matrix.GeneralLinearGroup.transvection i j hij a *
      Matrix.GeneralLinearGroup.transvection j k hjk b *
      (Matrix.GeneralLinearGroup.transvection i j hij a)⁻¹ *
      (Matrix.GeneralLinearGroup.transvection j k hjk b)⁻¹ =
        Matrix.GeneralLinearGroup.transvection i k hik (a * b) := by
  apply Units.ext
  change ((1 + Matrix.single i j a) * (1 + Matrix.single j k b)) *
      (1 + Matrix.single i j (-a)) * (1 + Matrix.single j k (-b)) =
    1 + Matrix.single i k (a * b)
  simp [mul_add, add_mul, hij.symm, hjk.symm, hik.symm, ← Matrix.single_neg]
  abel

theorem elem_commutator (r : Root) (a b : R) :
    elem r a * elem (right r) b * (elem r a)⁻¹ * (elem (right r) b)⁻¹ =
      elem (across r) (a * b) :=
  chain_commutator r.property (third_ne_target r).symm (third_ne_source r).symm a b

theorem elem_commutator_across (r : Root) (a b : R) :
    elem (across r) a * elem (reverse (right r)) b *
      (elem (across r) a)⁻¹ * (elem (reverse (right r)) b)⁻¹ = elem r (a * b) :=
  chain_commutator (third_ne_source r).symm (third_ne_target r) r.property a b

theorem map_elem {S : Type*} [CommRing S] (f : R →+* S) (r : Root) (c : R) :
    Matrix.GeneralLinearGroup.map f (elem r c) = elem r (f c) := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.map, coe_elem, Matrix.map_add, Matrix.map_one,
    Matrix.map_single]

end ThomGame.ElementaryMatrix
