module

public import ThomGame.Analysis.MatrixOperatorBounds
public import Mathlib.Algebra.Star.Subalgebra

/-!
# The star algebra of uniformly operator-bounded matrix sequences

The algebra consists of actual complex matrices of the prescribed
dimensions. Boundedness uses their Euclidean operator norm and is uniform
over the index set. Every sequence of unitaries belongs to this algebra.
-/

@[expose] public section
namespace ThomGame.Analysis

variable {ι : Type*} (dims : ι → Nat)

abbrev MatrixSequence := (i : ι) → CMatrix (dims i)

def OperatorBounded (A : MatrixSequence dims) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ i, matrixOpNorm (A i) ≤ K

def boundedMatrixAlgebra : StarSubalgebra ℂ (MatrixSequence dims) where
  carrier := OperatorBounded dims
  zero_mem' := ⟨0, le_rfl, fun _ => le_of_eq matrixOpNorm_zero⟩
  one_mem' := ⟨1, zero_le_one, fun _ => matrixOpNorm_one_le⟩
  add_mem' := by
    rintro A B ⟨a, ha, hA⟩ ⟨b, hb, hB⟩
    exact ⟨a + b, add_nonneg ha hb, fun i => (matrixOpNorm_add_le _ _).trans (add_le_add (hA i) (hB i))⟩
  mul_mem' := by
    rintro A B ⟨a, ha, hA⟩ ⟨b, hb, hB⟩
    exact ⟨a * b, mul_nonneg ha hb, fun i => (matrixOpNorm_mul_le _ _).trans
      (mul_le_mul (hA i) (hB i) (matrixOpNorm_nonneg _) ha)⟩
  algebraMap_mem' := by
    intro c
    refine ⟨‖c‖, norm_nonneg _, ?_⟩
    intro i
    change matrixOpNorm (algebraMap ℂ (CMatrix (dims i)) c) ≤ ‖c‖
    rw [Algebra.algebraMap_eq_smul_one, matrixOpNorm_smul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (matrixOpNorm_one_le (d := dims i)) (norm_nonneg c)
  star_mem' := by
    rintro A ⟨a, ha, hA⟩
    refine ⟨a, ha, ?_⟩
    intro i
    simpa only [Pi.star_apply, matrixOpNorm_star] using hA i

abbrev BoundedMatrixSequence := boundedMatrixAlgebra dims

theorem BoundedMatrixSequence.bound (A : BoundedMatrixSequence dims) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i, matrixOpNorm (A.val i) ≤ K := A.property

def boundedUnitarySequence (U : (i : ι) → UnitaryMatrix (dims i)) : BoundedMatrixSequence dims :=
  ⟨fun i => (U i).val, 1, zero_le_one, fun i => matrixOpNorm_unitary_le (U i)⟩

@[simp] theorem boundedUnitarySequence_apply (U : (i : ι) → UnitaryMatrix (dims i)) (i : ι) :
    (boundedUnitarySequence dims U).val i = (U i).val := rfl

@[simp] theorem boundedUnitarySequence_one : boundedUnitarySequence dims (fun _ => 1) = 1 := rfl

@[simp] theorem boundedUnitarySequence_mul (U V : (i : ι) → UnitaryMatrix (dims i)) :
    boundedUnitarySequence dims (fun i => U i * V i) =
      boundedUnitarySequence dims U * boundedUnitarySequence dims V := rfl

theorem boundedUnitarySequence_star_mul (U : (i : ι) → UnitaryMatrix (dims i)) :
    star (boundedUnitarySequence dims U) * boundedUnitarySequence dims U = 1 := by
  apply Subtype.ext
  exact funext fun i => (U i).property.1

theorem boundedUnitarySequence_mul_star (U : (i : ι) → UnitaryMatrix (dims i)) :
    boundedUnitarySequence dims U * star (boundedUnitarySequence dims U) = 1 := by
  apply Subtype.ext
  exact funext fun i => (U i).property.2

end ThomGame.Analysis
