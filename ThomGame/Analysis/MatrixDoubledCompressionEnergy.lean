module

public import ThomGame.Analysis.MatrixPartitionUnitaryTuple

/-!
# The actual compressed energy is dominated by the doubled tuple energy

Concatenation is the tuple of length 2h, so its lazy weight is 1/(8h).
The average identity in a corner gives the commutator estimate for
every matrix in that corner, including all of its projections.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d h : Nat}

noncomputable def matrixCompressedCoordinateEnergy (U : Fin h → UnitaryMatrix d)
    (q X : CMatrix d) : ℝ :=
  lazyMarkovWeight h * ∑ j, hsNorm ((q * (U j).val * q) * X - X * (q * (U j).val * q)) ^ 2

theorem matrixCompressedCoordinateEnergy_nonneg (U : Fin h → UnitaryMatrix d) (q X : CMatrix d) :
    0 ≤ matrixCompressedCoordinateEnergy U q X :=
  mul_nonneg (lazyMarkovWeight_nonneg h) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem hsNorm_compressed_commutator_le_pair {q U V W X : CMatrix d}
    (hV : Commute q V) (hW : Commute q W) (havg : q * V + q * W = (2 : ℂ) • (q * U * q))
    (hleft : q * X = X) (hright : X * q = X) :
    2 * hsNorm ((q * U * q) * X - X * (q * U * q)) ^ 2 ≤
      hsNorm (V * X - X * V) ^ 2 + hsNorm (W * X - X * W) ^ 2 := by
  have hlV : (q * V) * X = V * X := by rw [hV.eq, Matrix.mul_assoc, hleft]
  have hlW : (q * W) * X = W * X := by rw [hW.eq, Matrix.mul_assoc, hleft]
  have hrV : X * (q * V) = X * V := by rw [← Matrix.mul_assoc, hright]
  have hrW : X * (q * W) = X * W := by rw [← Matrix.mul_assoc, hright]
  have he : (2 : ℂ) • ((q * U * q) * X - X * (q * U * q)) =
      (V * X - X * V) + (W * X - X * W) := by
    calc
      _ = ((2 : ℂ) • (q * U * q)) * X - X * ((2 : ℂ) • (q * U * q)) := by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_sub]
      _ = (q * V + q * W) * X - X * (q * V + q * W) := by rw [havg]
      _ = _ := by rw [Matrix.add_mul, Matrix.mul_add, hlV, hlW, hrV, hrW]; abel
  have hn := congrArg (fun Y : CMatrix d => hsNorm Y ^ 2) he
  rw [hsNorm_smul, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num] at hn
  have hh := rectHSNorm_add_sq_le d (V * X - X * V) (W * X - X * W)
  simp only [rectHSNorm_eq_hsNorm] at hh
  nlinarith only [hn, hh]

variable [NeZero h]

theorem matrixCoordinateEnergy_append (V W : Fin h → UnitaryMatrix d) (X : CMatrix d) :
    matrixCoordinateEnergy (Fin.append V W) X =
      (1 / 2 : ℝ) * (matrixCoordinateEnergy V X + matrixCoordinateEnergy W X) := by
  have hw : lazyMarkovWeight (h + h) = (1 / 2 : ℝ) * lazyMarkovWeight h := by
    unfold lazyMarkovWeight
    push_cast
    have hh : (h : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne h)
    field_simp
    ring
  simp only [matrixCoordinateEnergy, Fin.sum_univ_add, Fin.append_left, Fin.append_right, hw]
  ring

theorem matrixCompressedCoordinateEnergy_le_doubled (U V W : Fin h → UnitaryMatrix d) (q X : CMatrix d)
    (hV : ∀ j, Commute q (V j).val) (hW : ∀ j, Commute q (W j).val)
    (havg : ∀ j, q * (V j).val + q * (W j).val = (2 : ℂ) • (q * (U j).val * q))
    (hleft : q * X = X) (hright : X * q = X) :
    matrixCompressedCoordinateEnergy U q X ≤ matrixCoordinateEnergy (Fin.append V W) X := by
  have hj (j : Fin h) : hsNorm ((q * (U j).val * q) * X - X * (q * (U j).val * q)) ^ 2 ≤
      (1 / 2 : ℝ) * (hsNorm ((V j).val * X - X * (V j).val) ^ 2 +
        hsNorm ((W j).val * X - X * (W j).val) ^ 2) := by
    have hh := hsNorm_compressed_commutator_le_pair (hV j) (hW j) (havg j) hleft hright
    linarith only [hh]
  calc
    _ ≤ lazyMarkovWeight h * ∑ j, (1 / 2 : ℝ) *
        (hsNorm ((V j).val * X - X * (V j).val) ^ 2 + hsNorm ((W j).val * X - X * (W j).val) ^ 2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hj j) (lazyMarkovWeight_nonneg h)
    _ = _ := by
      rw [matrixCoordinateEnergy_append]
      simp only [matrixCoordinateEnergy, ← Finset.mul_sum, Finset.sum_add_distrib]
      ring

theorem exists_matrixPartition_doubled_correction {μ : Type*} [Fintype μ] (E : μ → CMatrix d)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (hsum : ∑ i, E i = 1) (U : Fin h → UnitaryMatrix d) (bad : μ) :
    ∃ T : Fin (h + h) → UnitaryMatrix d,
      (∀ i j, Commute (E i) (T j).val) ∧
      (∀ j, E bad * (T j).val = E bad) ∧
      (∀ i, i ≠ bad → ∀ X : CMatrix d, E i * X = X → X * E i = X →
        matrixCompressedCoordinateEnergy U (E i) X ≤ matrixCoordinateEnergy T X) ∧
      (∑ j, hsNorm ((T j).val - (Fin.append U U j).val) ^ 2) ≤
        8 * (h : ℝ) * (∑ i, matrixCoordinateEnergy U (E i)) + 8 * (h : ℝ) * matrixTraceReal d (E bad) := by
  obtain ⟨V, W, hVc, hWc, hVb, hWb, havg, hdist⟩ := exists_matrixPartition_unitary_tuple E hE horth hsum U bad
  refine ⟨Fin.append V W, ?_, ?_, ?_, ?_⟩
  · intro i j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simpa only [Fin.append_left] using hVc i k
    · simpa only [Fin.append_right] using hWc i k
  · intro j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simpa only [Fin.append_left] using hVb k
    · simpa only [Fin.append_right] using hWb k
  · intro i hib X hleft hright
    exact matrixCompressedCoordinateEnergy_le_doubled U V W (E i) X (hVc i) (hWc i) (havg i hib) hleft hright
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [← Finset.sum_add_distrib]
    exact hdist

end ThomGame.Analysis
