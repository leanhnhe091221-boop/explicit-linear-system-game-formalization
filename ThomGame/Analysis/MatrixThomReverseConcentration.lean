module

public import ThomGame.Analysis.MatrixThomScaleConcentration
public import ThomGame.Analysis.MatrixThomReverseTransfer

/-!
# Actual reverse inclusion from corrected concentration

Dimension-zero corrected coordinates are handled directly. Thus the
limit theorem needs no positivity assumption on the corrected ranks.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

theorem matrixThom_reverseInclusion_center_near_general
    {d : Nat} [NeZero d] {A B D : StarSubalgebra ℂ (CMatrix d)} {ε : ℝ}
    (S : MatrixThomSpectralData A B D ε)
    (P : MatrixSubalgebraStarBlocks B)
    (R : MatrixSubalgebraStarBlocks (StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))))
    (hDB : D ≤ B) (F : MatrixSubalgebraStarBlocks D)
    (s : Fin F.count → ℝ) (hs : ∀ i, 0 < s i) :
    MatrixNearInclusion S.correctedTargetAlgebra S.correctedSourceAlgebra
      (4 * Real.sqrt (S.retainedScaleConcentration P R hDB F s)) := by
  by_cases hm : S.cut.rank = 0
  · intro X _ _
    have hX : X = 0 := by
      ext i j
      have hi := i.isLt
      omega
    refine ⟨0, S.correctedSourceAlgebra.zero_mem, ?_⟩
    rw [hX, sub_self, hsNorm_zero]
    positivity
  · let : NeZero S.cut.rank := ⟨hm⟩
    exact matrixThom_reverseInclusion_center_near S P R hDB F s hs

theorem matrixThom_reverseInclusion_original_tendsto
    {ι : Type*} (dims : ι → Nat) [∀ n, NeZero (dims n)]
    {A B D : (n : ι) → StarSubalgebra ℂ (CMatrix (dims n))} {ε : ι → ℝ}
    (S : (n : ι) → MatrixThomSpectralData (A n) (B n) (D n) (ε n))
    (P : (n : ι) → MatrixSubalgebraStarBlocks (B n))
    (R : (n : ι) → MatrixSubalgebraStarBlocks
      (StarSubalgebra.centralizer ℂ (A n : Set (CMatrix (dims n)))))
    (hDB : ∀ n, D n ≤ B n) (F : (n : ι) → MatrixSubalgebraStarBlocks (D n))
    (s : (n : ι) → Fin (F n).count → ℝ) (hs : ∀ n i, 0 < s n i)
    (L : Filter ι) (hε : Tendsto ε L (𝓝 0))
    (hε0 : ∀ n, 0 ≤ ε n) (hBA : ∀ n, MatrixNearInclusion (B n) (A n) (ε n))
    (hc : Tendsto (fun n => (S n).retainedScaleConcentration (P n) (R n) (hDB n) (F n) (s n)) L (𝓝 0)) :
    Tendsto (fun n => matrixNearInclusionError (A n) (B n)) L (𝓝 0) := by
  apply matrixThom_reverse_nearInclusion_tendsto dims S L hε
    (δ := fun n => 4 * Real.sqrt ((S n).retainedScaleConcentration (P n) (R n) (hDB n) (F n) (s n)))
    (by simpa only [Real.sqrt_zero, mul_zero] using hc.sqrt.const_mul 4) hε0 hBA
  exact fun n => matrixThom_reverseInclusion_center_near_general (S n) (P n) (R n) (hDB n) (F n) (s n) (hs n)

end ThomGame.Analysis
