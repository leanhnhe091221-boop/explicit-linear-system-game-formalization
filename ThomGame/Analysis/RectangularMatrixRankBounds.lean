module

public import ThomGame.Analysis.NormalizedHilbertSchmidt
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Rank subadditivity for rectangular complex matrices
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators

variable {m n : Nat}

theorem rectangularMatrix_rank_add_le (X Y : Matrix (Fin m) (Fin n) ℂ) :
    (X + Y).rank ≤ X.rank + Y.rank := by
  have hle := Submodule.finrank_mono (LinearMap.range_add_le X.mulVecLin Y.mulVecLin)
  have he := Submodule.finrank_sup_add_finrank_inf_eq X.mulVecLin.range Y.mulVecLin.range
  change Module.finrank ℂ (X + Y).mulVecLin.range ≤ _
  rw [Matrix.mulVecLin_add]
  change Module.finrank ℂ (X.mulVecLin + Y.mulVecLin).range ≤
    Module.finrank ℂ X.mulVecLin.range + Module.finrank ℂ Y.mulVecLin.range
  omega

theorem rectangularMatrix_rank_sum_le {ι : Type*} (s : Finset ι)
    (X : ι → Matrix (Fin m) (Fin n) ℂ) : (∑ i ∈ s, X i).rank ≤ ∑ i ∈ s, (X i).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (rectangularMatrix_rank_add_le _ _).trans (Nat.add_le_add_left ih _)

end ThomGame.Analysis
