module

public import ThomGame.Analysis.MatrixBoundedScaleRankChanges

/-!
# Rank-change convergence for bounded scales along arbitrary filters

Only the displayed weighted rank errors must vanish. There is no
uniform bound on the positive regularizing matrices or their inverses.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix Filter
open scoped BigOperators Topology Matrix.Norms.L2Operator

variable {ι : Type*} (dims r : ι → Nat)
    (D A : (n : ι) → StarSubalgebra ℂ (CMatrix (dims n)))
    (P : (n : ι) → MatrixSubalgebraStarBlocks (D n))
    (Q : (n : ι) → MatrixSubalgebraStarBlocks (A n))
    (hDA : ∀ n, D n ≤ A n)
    (s : (n : ι) → Fin (P n).count → ℝ) (hs : ∀ n i, 0 < s n i)
    (old : (n : ι) → Fin (Q n).count → Nat) (hold : ∀ n j, 0 < old n j)

include hDA hs hold in
theorem matrixBoundedScale_sizeChange_tendsto (L : Filter ι)
    (hchange : Tendsto (fun n =>
      (∑ j, (matrixStarRepresentationMultiplicity (A n) (Q n) (A n).subtype j : ℝ) *
        |(old n j : ℝ) - (Q n).size j|) / r n) L (𝓝 0)) :
    Tendsto (fun n => rectHSNorm (r n)
      (matrixBoundedScale (matrixStarBlockScalar (A n) (Q n) (fun j => (old n j : ℝ) /
        matrixStarRepresentationMultiplicity (A n) (Q n) (A n).subtype j)) (matrixStarBlockScalar (D n) (P n) (s n)) -
      matrixBoundedScale (matrixSubalgebraScale (A n) (Q n)) (matrixStarBlockScalar (D n) (P n) (s n)))) L (𝓝 0) := by
  have he := squeeze_zero (fun n => sq_nonneg (rectHSNorm (r n)
      (matrixBoundedScale (matrixStarBlockScalar (A n) (Q n) (fun j => (old n j : ℝ) /
        matrixStarRepresentationMultiplicity (A n) (Q n) (A n).subtype j)) (matrixStarBlockScalar (D n) (P n) (s n)) -
      matrixBoundedScale (matrixSubalgebraScale (A n) (Q n)) (matrixStarBlockScalar (D n) (P n) (s n)))))
    (fun n => matrixBoundedScale_sizeChange (D n) (A n) (P n) (Q n) (hDA n) (s n) (hs n) (r n) (old n) (hold n)) hchange
  simpa only [Real.sqrt_sq (rectHSNorm_nonneg _ _), Real.sqrt_zero] using he.sqrt

include hDA hs hold in
theorem matrixBoundedScale_multiplicityChange_tendsto (L : Filter ι)
    (hchange : Tendsto (fun n =>
      (∑ j, ((Q n).size j : ℝ) *
        |(old n j : ℝ) - matrixStarRepresentationMultiplicity (A n) (Q n) (A n).subtype j|) / r n) L (𝓝 0)) :
    Tendsto (fun n => rectHSNorm (r n)
      (matrixBoundedScale (matrixSubalgebraScale (A n) (Q n)) (matrixStarBlockScalar (D n) (P n) (s n)) -
      matrixBoundedScale (matrixStarBlockScalar (A n) (Q n) (fun j => ((Q n).size j : ℝ) / old n j))
        (matrixStarBlockScalar (D n) (P n) (s n)))) L (𝓝 0) := by
  have he := squeeze_zero (fun n => sq_nonneg (rectHSNorm (r n)
      (matrixBoundedScale (matrixSubalgebraScale (A n) (Q n)) (matrixStarBlockScalar (D n) (P n) (s n)) -
      matrixBoundedScale (matrixStarBlockScalar (A n) (Q n) (fun j => ((Q n).size j : ℝ) / old n j))
        (matrixStarBlockScalar (D n) (P n) (s n)))))
    (fun n => matrixBoundedScale_multiplicityChange (D n) (A n) (P n) (Q n) (hDA n) (s n) (hs n) (r n) (old n) (hold n)) hchange
  simpa only [Real.sqrt_sq (rectHSNorm_nonneg _ _), Real.sqrt_zero] using he.sqrt

end ThomGame.Analysis
