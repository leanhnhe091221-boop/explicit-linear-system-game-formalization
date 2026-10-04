module

public import ThomGame.Analysis.UnitaryHilbertSchmidt
public import Mathlib.Tactic.Linarith

/-! The finite-dimensional norm contradiction at the final HNN bridge. -/

@[expose] public section
namespace ThomGame.Analysis

variable {d : Nat}

theorem unitary_hnn_bridge_length (Z W J : UnitaryMatrix d) :
    unitaryLength J ≤ unitaryDist (Z * W * Z⁻¹) (W * J) + 2 * unitaryLength W := by
  have hfirst := unitaryDist_triangle (W * J) (Z * W * Z⁻¹) W
  have hsecond := unitaryDist_triangle (Z * W * Z⁻¹) 1 W
  have he : unitaryDist (W * J) W = unitaryLength J := by
    simpa only [mul_one, unitaryLength] using unitaryDist_mul_left W J 1
  rw [he, unitaryDist_comm (W * J)] at hfirst
  have hz : unitaryDist (Z * W * Z⁻¹) 1 = unitaryLength W := unitaryLength_conj Z W
  have hw : unitaryDist 1 W = unitaryLength W := unitaryDist_comm 1 W
  rw [hz, hw] at hsecond
  linarith

theorem unitary_hnn_bridge_inequality [NeZero d] (Z W J : UnitaryMatrix d) :
    2 ≤ unitaryDist J (-1) + unitaryDist (Z * W * Z⁻¹) (W * J) +
      2 * unitaryLength W := by
  have ht := unitaryDist_triangle (-1 : UnitaryMatrix d) J 1
  change unitaryLength (-1 : UnitaryMatrix d) ≤ unitaryDist (-1) J + unitaryLength J at ht
  rw [unitaryLength_neg_one, unitaryDist_comm (-1)] at ht
  have hJ := unitary_hnn_bridge_length Z W J
  linarith

/-- The exact numeric contradiction used after the wheel and double estimates. -/
theorem unitary_hnn_bridge_impossible [NeZero d] (Z W J : UnitaryMatrix d)
    {η δ : ℝ} (hδ : δ ≤ 1) (hη : η ≤ δ / 168)
    (hJ : unitaryDist J (-1) ≤ 12 * η)
    (hhnn : unitaryDist (Z * W * Z⁻¹) (W * J) ≤ 180 * η)
    (hW : unitaryLength W ≤ 1 / 4) : False := by
  have h := unitary_hnn_bridge_inequality Z W J
  linarith

end ThomGame.Analysis
