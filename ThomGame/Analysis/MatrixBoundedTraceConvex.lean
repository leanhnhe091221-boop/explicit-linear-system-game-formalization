module

public import ThomGame.Analysis.MatrixBoundedTraceBall
public import Mathlib.Analysis.LocallyConvex.WeakSpace

/-!
# Weak closedness of trace vectors with uniformly bounded representatives

The represented ball is convex over the reals. Its trace-norm closedness
therefore implies closedness in the actual weak topology of the Hilbert
space, using the geometric Hahn--Banach theorem from mathlib.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable {ι : Type*} (dims : ι → Nat) (hd : ∀ i, 0 < dims i) (U : Ultrafilter ι)

theorem matrixBoundedTraceBall_convex (K : ℝ) :
    Convex ℝ (matrixBoundedTraceBall dims hd U K) := by
  rintro x ⟨A, hA, rfl⟩ y ⟨B, hB, rfl⟩ a b ha hb hab
  refine ⟨(a : ℂ) • A + (b : ℂ) • B, ?_, ?_⟩
  · intro i
    change matrixOpNorm ((a : ℂ) • A.val i + (b : ℂ) • B.val i) ≤ K
    calc
      _ ≤ matrixOpNorm ((a : ℂ) • A.val i) + matrixOpNorm ((b : ℂ) • B.val i) :=
        matrixOpNorm_add_le _ _
      _ = a * matrixOpNorm (A.val i) + b * matrixOpNorm (B.val i) := by
        rw [matrixOpNorm_smul, matrixOpNorm_smul, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ a * K + b * K := add_le_add (mul_le_mul_of_nonneg_left (hA i) ha)
        (mul_le_mul_of_nonneg_left (hB i) hb)
      _ = K := by rw [← add_mul, hab, one_mul]
  · change matrixHilbertEmbedding dims hd U
      (matrixQuotientStarAlgHom dims (U : Filter ι) ((a : ℂ) • A + (b : ℂ) • B)) = _
    simp only [map_add, map_smul]
    simp only [Complex.coe_smul]
    rfl

theorem matrixBoundedTraceBall_weak_isClosed (dims : Nat → Nat) (hd : ∀ n, 0 < dims n)
    (U : Ultrafilter Nat) (hU : (U : Filter Nat) ≤ atTop) (K : ℝ) (hK : 0 ≤ K) :
    IsClosed ((toWeakSpace ℂ (MatrixTraceHilbert dims hd U)) ''
      matrixBoundedTraceBall dims hd U K) := by
  have he := (matrixBoundedTraceBall_convex dims hd U K).toWeakSpace_closure ℂ
  rw [(matrixBoundedTraceBall_isClosed dims hd U hU K hK).closure_eq] at he
  rw [he]
  exact isClosed_closure

end ThomGame.Analysis
