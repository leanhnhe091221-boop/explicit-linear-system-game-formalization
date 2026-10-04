module

public import ThomGame.Analysis.MatrixProjectionPieces
public import ThomGame.Analysis.MatrixCommutatorProducts

/-!
# Boundary energy of the pieces returned to the original space

The product rule uses both actual compressed-unitary errors and the
contractivity of each block. Summing gives the inequality immediately
preceding ALT (3.14). Initial projections cost a further factor four.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {μ ι : Type*} [Fintype μ] [Fintype ι] [DecidableEq μ] [DecidableEq ι]

theorem matrixProjectionPiece_commutator_sq_le (r : Nat) {q : μ → Matrix ι ι ℂ}
    (hq : ∀ i, IsStarProjection (q i)) {Z : Matrix (MatrixProjectionSumIndex hq) ι ℂ}
    (hZ : IsStarProjection (Zᴴ * Z))
    (hcomm : ∀ i, Commute (Z * Zᴴ) (matrixBlockLabel (κ := fun i => MatrixProjectionRangeIndex (hq i)) i))
    (u : Matrix.unitaryGroup ι ℂ) (i : μ) :
    rectHSNorm r (u.val * matrixProjectionPiece hq Z i - matrixProjectionPiece hq Z i * u.val) ^ 2 ≤
      2 * rectHSNorm r (u.val * q i - q i * u.val) ^ 2 +
        2 * rectHSNorm r ((matrixProjectionRangeUnitary r (hq i) u).val * matrixBlockComponent Z i -
          matrixBlockComponent Z i * u.val) ^ 2 := by
  let F := matrixProjectionFrame (hq i)
  let B := matrixBlockComponent Z i
  let v := matrixProjectionRangeUnitary r (hq i) u
  have he : u.val * matrixProjectionPiece hq Z i - matrixProjectionPiece hq Z i * u.val =
      (u.val * F - F * v.val) * B + F * (v.val * B - B * u.val) := by
    simp only [matrixProjectionPiece, F, B, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    abel
  have hfirst := rectHSNorm_mul_sq_le_of_partialIsometry r (u.val * F - F * v.val)
    (matrixBlockComponent_initial_projection hZ hcomm i)
  have hlocal := (matrixProjectionRangeUnitary_errors r (hq i) u).2
  have hsum := rectHSNorm_add_sq_le r ((u.val * F - F * v.val) * B) (F * (v.val * B - B * u.val))
  rw [← he, rectHSNorm_frame_mul r (matrixProjectionFrame_initial (hq i))] at hsum
  change rectHSNorm r ((u.val * F - F * v.val) * B) ^ 2 ≤ rectHSNorm r (u.val * F - F * v.val) ^ 2 at hfirst
  change rectHSNorm r (u.val * F - F * v.val) ^ 2 ≤ rectHSNorm r (u.val * q i - q i * u.val) ^ 2 at hlocal
  linarith

theorem matrixProjectionPiece_energy_le {h : Nat} (r : Nat) {q : μ → Matrix ι ι ℂ}
    (hq : ∀ i, IsStarProjection (q i)) {Z : Matrix (MatrixProjectionSumIndex hq) ι ℂ}
    (hZ : IsStarProjection (Zᴴ * Z))
    (hcomm : ∀ i, Commute (Z * Zᴴ) (matrixBlockLabel (κ := fun i => MatrixProjectionRangeIndex (hq i)) i))
    (U : Fin h → Matrix.unitaryGroup ι ℂ) :
    (∑ i, matrixIntertwiningEnergy r U U (matrixProjectionPiece hq Z i)) ≤
      2 * (∑ i, matrixIntertwiningEnergy r U U (q i)) +
        2 * matrixIntertwiningEnergy r U (fun j => matrixProjectionBlockUnitary r hq (U j)) Z := by
  have hi (i : μ) : matrixIntertwiningEnergy r U U (matrixProjectionPiece hq Z i) ≤
      2 * matrixIntertwiningEnergy r U U (q i) +
        2 * matrixIntertwiningEnergy r U (fun j => matrixProjectionRangeUnitary r (hq i) (U j)) (matrixBlockComponent Z i) := by
    have he := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := Finset.univ) fun j _ =>
      matrixProjectionPiece_commutator_sq_le r hq hZ hcomm (U j) i) (lazyMarkovWeight_nonneg h)
    simpa only [matrixIntertwiningEnergy, Finset.sum_add_distrib, ← Finset.mul_sum,
      mul_add, mul_left_comm (lazyMarkovWeight h) 2] using he
  have he := Finset.sum_le_sum (s := Finset.univ) fun i _ => hi i
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, matrixBlockComponent_energy] at he
  exact he

omit [Fintype μ] [Fintype ι] [DecidableEq μ] [DecidableEq ι] in
theorem matrixPartialIsometry_norm_le_one {d : Nat} {X : CMatrix d}
    (hX : IsStarProjection (Xᴴ * X)) : matrixOpNorm X ≤ 1 := by
  have he := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hX.nonneg).mpr hX.le_one
  change ‖star X * X‖ ≤ 1 at he
  rw [CStarRing.norm_star_mul_self] at he
  change ‖X‖ ≤ 1
  nlinarith [norm_nonneg X]

omit [Fintype μ] [Fintype ι] [DecidableEq μ] [DecidableEq ι] in
theorem matrixCoordinateEnergy_partialIsometry_initial_le {d h : Nat}
    (U : Fin h → UnitaryMatrix d) {X : CMatrix d} (hX : IsStarProjection (Xᴴ * X)) :
    matrixCoordinateEnergy U (Xᴴ * X) ≤ 4 * matrixCoordinateEnergy U X := by
  have hn : matrixOpNorm (star X) ≤ 1 := by rw [matrixOpNorm_star]; exact matrixPartialIsometry_norm_le_one hX
  have hj (j : Fin h) := hsNorm_unitary_commutator_gram_le (U j) (star X) hn
  simp only [star_star, hsNorm_unitary_commutator_star] at hj
  have hs (j : Fin h) := (sq_le_sq₀ (hsNorm_nonneg _) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hsNorm_nonneg _))).mpr (hj j)
  simp only [mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] at hs
  have he := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := Finset.univ) fun j _ => hs j) (lazyMarkovWeight_nonneg h)
  simpa only [matrixCoordinateEnergy, Matrix.star_eq_conjTranspose, ← Finset.mul_sum,
    mul_left_comm (lazyMarkovWeight h)] using he

end ThomGame.Analysis
