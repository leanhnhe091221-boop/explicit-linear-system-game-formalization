module

public import ThomGame.Analysis.NormalizedHilbertSchmidt
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Trace

/-!
# Trace and rank of algebraic matrix idempotents

The trace equals the rank even when an idempotent is not self-adjoint.
This permits exact multiplicity computations before choosing orthonormal
block bases.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators

theorem matrixIdempotent_trace_eq_rank {d : Nat} {X : CMatrix d}
    (hX : IsIdempotentElem X) : X.trace = (X.rank : ℂ) := by
  have hf : IsIdempotentElem X.mulVecLin := by
    change X.mulVecLin.comp X.mulVecLin = X.mulVecLin
    rw [← Matrix.mulVecLin_mul, hX.eq]
  have he := (LinearMap.IsIdempotentElem.isProj_range X.mulVecLin hf).trace
  rw [← Matrix.toLin'_apply', Matrix.trace_toLin'_eq] at he
  exact he

theorem matrixIdempotent_rank_eq_of_trace_eq {d m : Nat} {X : CMatrix d} {Y : CMatrix m}
    (hX : IsIdempotentElem X) (hY : IsIdempotentElem Y) (htr : X.trace = Y.trace) : X.rank = Y.rank := by
  rw [matrixIdempotent_trace_eq_rank hX, matrixIdempotent_trace_eq_rank hY] at htr
  exact_mod_cast htr

theorem matrixIdempotent_rank_pos {d : Nat} {X : CMatrix d}
    (hX : IsIdempotentElem X) (hne : X ≠ 0) : 0 < X.rank := by
  apply Nat.pos_of_ne_zero
  intro hr
  have ht : X.trace = 0 := by rw [matrixIdempotent_trace_eq_rank hX, hr, Nat.cast_zero]
  have hf : IsIdempotentElem X.toLin' := hX.map Matrix.toLinAlgEquiv'
  have hz := LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hf
    (by simpa only [Matrix.trace_toLin'_eq] using ht)
  exact hne (Matrix.toLin'.injective (by simpa only [map_zero] using hz))

theorem matrixIdempotent_sum_rank {ι : Type*} [Fintype ι] {d : Nat}
    (X : ι → CMatrix d) (hX : ∀ i, IsIdempotentElem (X i))
    (hs : IsIdempotentElem (∑ i, X i)) : (∑ i, X i).rank = ∑ i, (X i).rank := by
  have he := Matrix.trace_sum Finset.univ X
  rw [matrixIdempotent_trace_eq_rank hs] at he
  simp only [matrixIdempotent_trace_eq_rank (hX _)] at he
  exact_mod_cast he

end ThomGame.Analysis
