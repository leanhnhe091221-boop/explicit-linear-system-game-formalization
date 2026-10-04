module

public import ThomGame.Analysis.BoundedMatrixSequences
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# The two-sided star-stable ideal of normalized 2-null matrix sequences

Uniform operator bounds, together with the actual mixed-norm estimates,
make left and right multiplication preserve convergence to zero in the
normalized Hilbert--Schmidt norm.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable {ι : Type*} (dims : ι → Nat) (L : Filter ι)

def matrixNullIdeal : Ideal (BoundedMatrixSequence dims) where
  carrier A := Tendsto (fun i => hsNorm (A.val i)) L (𝓝 0)
  zero_mem' := by
    change Tendsto (fun _ : ι => hsNorm 0) L (𝓝 0)
    simpa only [hsNorm_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : ℝ)) L (𝓝 0))
  add_mem' := by
    intro A B hA hB
    change Tendsto (fun i => hsNorm (A.val i)) L (𝓝 0) at hA
    change Tendsto (fun i => hsNorm (B.val i)) L (𝓝 0) at hB
    have ht := hA.add hB
    rw [zero_add] at ht
    exact squeeze_zero (fun i => hsNorm_nonneg _) (fun i => hsNorm_add_le _ _) ht
  smul_mem' := by
    intro B A hA
    change Tendsto (fun i => hsNorm (A.val i)) L (𝓝 0) at hA
    obtain ⟨K, _, hB⟩ := BoundedMatrixSequence.bound dims B
    have ht := hA.const_mul K
    rw [mul_zero] at ht
    exact squeeze_zero (fun i => hsNorm_nonneg _)
      (fun i => (hsNorm_mul_le_left (B.val i) (A.val i)).trans
        (mul_le_mul_of_nonneg_right (hB i) (hsNorm_nonneg _))) ht

instance matrixNullIdeal_twoSided : (matrixNullIdeal dims L).IsTwoSided where
  mul_mem_of_left B hA := by
    rename_i A
    change Tendsto (fun i => hsNorm (A.val i)) L (𝓝 0) at hA
    obtain ⟨K, _, hB⟩ := BoundedMatrixSequence.bound dims B
    have ht := hA.mul_const K
    rw [zero_mul] at ht
    exact squeeze_zero (fun i => hsNorm_nonneg _)
      (fun i => (hsNorm_mul_le_right (A.val i) (B.val i)).trans
        (mul_le_mul_of_nonneg_left (hB i) (hsNorm_nonneg _))) ht

theorem matrixNullIdeal_star (A : BoundedMatrixSequence dims) (hA : A ∈ matrixNullIdeal dims L) :
    star A ∈ matrixNullIdeal dims L := by
  change Tendsto (fun i => hsNorm (A.val i)) L (𝓝 0) at hA
  change Tendsto (fun i => hsNorm (star (A.val i))) L (𝓝 0)
  simpa only [Matrix.star_eq_conjTranspose, hsNorm_conjTranspose] using hA

abbrev MatrixTracialQuotient := BoundedMatrixSequence dims ⧸ matrixNullIdeal dims L

def matrixQuotientMk : BoundedMatrixSequence dims →+* MatrixTracialQuotient dims L :=
  Ideal.Quotient.mk _

theorem matrixQuotientMk_eq_zero_iff (A : BoundedMatrixSequence dims) :
    matrixQuotientMk dims L A = 0 ↔ Tendsto (fun i => hsNorm (A.val i)) L (𝓝 0) :=
  Ideal.Quotient.eq_zero_iff_mem

theorem matrixQuotientMk_eq_iff (A B : BoundedMatrixSequence dims) :
    matrixQuotientMk dims L A = matrixQuotientMk dims L B ↔
      Tendsto (fun i => hsNorm (A.val i - B.val i)) L (𝓝 0) :=
  Ideal.Quotient.eq

end ThomGame.Analysis
