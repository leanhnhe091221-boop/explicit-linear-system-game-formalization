module

public import ThomGame.Analysis.UnitaryHilbertSchmidt
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Group

/-! Quantitative row-word permutation estimates for actual unitary matrices. -/

@[expose] public section
namespace ThomGame.Analysis

variable {d : Nat}

theorem unitaryDist_swap (U V : UnitaryMatrix d) :
    unitaryDist (U * V) (V * U) = unitaryLength (U * V * U⁻¹ * V⁻¹) := by
  rw [unitaryDist_eq_length, mul_inv_rev, ← mul_assoc]

theorem unitaryLength_commutator_swap (U V : UnitaryMatrix d) :
    unitaryLength (U * V * U⁻¹ * V⁻¹) = unitaryLength (V * U * V⁻¹ * U⁻¹) := by
  rw [← unitaryDist_swap, ← unitaryDist_swap, unitaryDist_comm]

set_option maxHeartbeats 600000 in
/-- Each adjacent transposition costs at most delta; three suffice for any triple. -/
theorem unitaryTriple_permutation_bound (v : Fin 3 → UnitaryMatrix d) (δ : ℝ)
    (hδ : 0 ≤ δ) (hc : ∀ i j, unitaryDist (v i * v j) (v j * v i) ≤ δ)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    unitaryDist (v i * v j * v k) (v 0 * v 1 * v 2) ≤ 3 * δ := by
  have h102 : unitaryDist (v 1 * v 0 * v 2) (v 0 * v 1 * v 2) ≤ δ := by
    rw [unitaryDist_mul_right]
    exact hc 1 0
  have h021 : unitaryDist (v 0 * v 2 * v 1) (v 0 * v 1 * v 2) ≤ δ := by
    simp only [mul_assoc, unitaryDist_mul_left]
    exact hc 2 1
  have h120 : unitaryDist (v 1 * v 2 * v 0) (v 0 * v 1 * v 2) ≤ 2 * δ := by
    have h := unitaryDist_triangle (v 1 * v 2 * v 0) (v 1 * v 0 * v 2)
      (v 0 * v 1 * v 2)
    have hs : unitaryDist (v 1 * v 2 * v 0) (v 1 * v 0 * v 2) ≤ δ := by
      simp only [mul_assoc, unitaryDist_mul_left]
      exact hc 2 0
    linarith
  have h201 : unitaryDist (v 2 * v 0 * v 1) (v 0 * v 1 * v 2) ≤ 2 * δ := by
    have h := unitaryDist_triangle (v 2 * v 0 * v 1) (v 0 * v 2 * v 1)
      (v 0 * v 1 * v 2)
    have hs : unitaryDist (v 2 * v 0 * v 1) (v 0 * v 2 * v 1) ≤ δ := by
      rw [unitaryDist_mul_right]
      exact hc 2 0
    linarith
  have h210 : unitaryDist (v 2 * v 1 * v 0) (v 0 * v 1 * v 2) ≤ 3 * δ := by
    have h := unitaryDist_triangle (v 2 * v 1 * v 0) (v 1 * v 2 * v 0)
      (v 0 * v 1 * v 2)
    have hs : unitaryDist (v 2 * v 1 * v 0) (v 1 * v 2 * v 0) ≤ δ := by
      rw [unitaryDist_mul_right]
      exact hc 2 1
    linarith
  fin_cases i <;> fin_cases j <;> fin_cases k <;> try contradiction
  · change unitaryDist (v 0 * v 1 * v 2) (v 0 * v 1 * v 2) ≤ 3 * δ
    rw [unitaryDist_self]
    linarith only [hδ]
  · change unitaryDist (v 0 * v 2 * v 1) (v 0 * v 1 * v 2) ≤ 3 * δ
    linarith only [h021, hδ]
  · change unitaryDist (v 1 * v 0 * v 2) (v 0 * v 1 * v 2) ≤ 3 * δ
    linarith only [h102, hδ]
  · change unitaryDist (v 1 * v 2 * v 0) (v 0 * v 1 * v 2) ≤ 3 * δ
    linarith only [h120, hδ]
  · change unitaryDist (v 2 * v 0 * v 1) (v 0 * v 1 * v 2) ≤ 3 * δ
    linarith only [h201, hδ]
  · exact h210

theorem unitaryTriple_perm_bound (v : Fin 3 → UnitaryMatrix d) (σ : Equiv.Perm (Fin 3))
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hc : ∀ i j, unitaryLength (v i * v j * (v i)⁻¹ * (v j)⁻¹) ≤ δ) :
    unitaryDist (v (σ 0) * v (σ 1) * v (σ 2)) (v 0 * v 1 * v 2) ≤ 3 * δ :=
  unitaryTriple_permutation_bound v δ hδ (by simpa only [unitaryDist_swap] using hc)
    _ _ _ (σ.injective.ne (by decide)) (σ.injective.ne (by decide))
    (σ.injective.ne (by decide))

end ThomGame.Analysis
