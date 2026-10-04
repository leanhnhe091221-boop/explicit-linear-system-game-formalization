module

public import ThomGame.Analysis.MatrixResolventFactorCommutator

/-!
# Input energy controls the actual resolvent-difference family

Summing the local factor bounds and the full unitary resolvent estimate
removes the intermediate column energy. Averaging over the unitaries
retains a constant independent of dimension, family size and h.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

theorem resolvent_difference_total_bound {lam E e X Z : ℝ}
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hE : 0 ≤ E) (he : e ≤ E)
    (hZ : Z ≤ (292 / lam ^ 3) * E) (hX : X ≤ (32 / lam ^ 3) * e + (32 / lam) * Z) :
    X ≤ (9376 / lam ^ 4) * E := by
  have hc : 32 / lam ^ 3 + (32 / lam) * (292 / lam ^ 3) ≤ 9376 / lam ^ 4 := by
    apply (mul_le_mul_iff_right₀ (pow_pos hlam 4)).mp
    have hleft : lam ^ 4 * (32 / lam ^ 3 + (32 / lam) * (292 / lam ^ 3)) = 32 * lam + 9344 := by
      field_simp
      ring
    have hright : lam ^ 4 * (9376 / lam ^ 4) = 9376 := by field_simp
    rw [hleft, hright]
    linarith
  calc
    X ≤ (32 / lam ^ 3) * e + (32 / lam) * Z := hX
    _ ≤ (32 / lam ^ 3) * E + (32 / lam) * ((292 / lam ^ 3) * E) :=
      add_le_add (mul_le_mul_of_nonneg_left he (by positivity))
        (mul_le_mul_of_nonneg_left hZ (by positivity))
    _ = (32 / lam ^ 3 + (32 / lam) * (292 / lam ^ 3)) * E := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hE

variable {d h : Nat} [NeZero d]

theorem matrixResolventDifferenceFamily_commutator_sum_le {lam : ℝ} {P : CMatrix d}
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hP : IsStarProjection P)
    (F : Nat → CMatrix d) (hF : ∀ i, IsStarProjection (F i)) (U : UnitaryMatrix d) (n : Nat) :
    (∑ i ∈ Finset.range n, hsNorm (U.val * matrixResolventDifferenceFamily lam P F i -
      matrixResolventDifferenceFamily lam P F i * U.val) ^ 2) ≤
      (9376 / lam ^ 4) * (hsNorm (U.val * P - P * U.val) ^ 2 +
        ∑ i ∈ Finset.range n, hsNorm (U.val * F i - F i * U.val) ^ 2) := by
  have hr := matrixResolvent_unitary_family_bound_initial hlam hlam1 hP F hF U n
  have he := Finset.sum_le_sum (s := Finset.range n) (fun i _ =>
    hsNorm_projection_resolvent_difference_commutator_sq_le hlam hlam1
      (matrixProjectionPartialSum_nonneg hP.nonneg F hF i) (hF i) U)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at he
  exact resolvent_difference_total_bound hlam hlam1
    (add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
    (le_add_of_nonneg_left (sq_nonneg _)) hr he

theorem matrixResolventDifferenceFamily_energy_sum_le {lam : ℝ} {P : CMatrix d}
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hP : IsStarProjection P)
    (F : Nat → CMatrix d) (hF : ∀ i, IsStarProjection (F i)) (U : Fin h → UnitaryMatrix d) (n : Nat) :
    (∑ i ∈ Finset.range n, matrixCoordinateEnergy U (matrixResolventDifferenceFamily lam P F i)) ≤
      (9376 / lam ^ 4) * (matrixCoordinateEnergy U P +
        ∑ i ∈ Finset.range n, matrixCoordinateEnergy U (F i)) := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    matrixResolventDifferenceFamily_commutator_sum_le hlam hlam1 hP F hF (U j) n)
  have hw := mul_le_mul_of_nonneg_left hs (lazyMarkovWeight_nonneg h)
  unfold matrixCoordinateEnergy
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hw ⊢
  rw [Finset.sum_comm] at hw
  have he : (∑ j : Fin h, ∑ i ∈ Finset.range n, hsNorm ((U j).val * F i - F i * (U j).val) ^ 2) =
      ∑ i ∈ Finset.range n, ∑ j : Fin h, hsNorm ((U j).val * F i - F i * (U j).val) ^ 2 :=
    Finset.sum_comm
  rw [he] at hw
  convert hw using 1
  ring

theorem matrixResolventDifferenceFamily_energy_fin_sum_le {lam : ℝ} {P : CMatrix d}
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hP : IsStarProjection P)
    (F : Nat → CMatrix d) (hF : ∀ i, IsStarProjection (F i)) (U : Fin h → UnitaryMatrix d) (n : Nat) :
    (∑ i : Fin n, matrixCoordinateEnergy U (matrixResolventDifferenceFamily lam P F i)) ≤
      (9376 / lam ^ 4) * (matrixCoordinateEnergy U P +
        ∑ i ∈ Finset.range n, matrixCoordinateEnergy U (F i)) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => matrixCoordinateEnergy U (matrixResolventDifferenceFamily lam P F i))]
  exact matrixResolventDifferenceFamily_energy_sum_le hlam hlam1 hP F hF U n

end ThomGame.Analysis
