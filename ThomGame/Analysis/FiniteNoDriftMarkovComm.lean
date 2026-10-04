module

public import ThomGame.Analysis.FiniteNoDriftShearAction

/-! Convex averaging propagates finite commutator bounds. -/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {d : Nat}

theorem finiteNoDriftComm_add (G : UnitaryMatrix d) (X Y : CMatrix d) :
    finiteNoDriftComm G (X + Y) ≤ finiteNoDriftComm G X + finiteNoDriftComm G Y := by
  have he : G.val * (X + Y) - (X + Y) * G.val = (G.val * X - X * G.val) + (G.val * Y - Y * G.val) := by
    noncomm_ring
  unfold finiteNoDriftComm
  rw [he]
  exact hsNorm_add_le _ _

theorem finiteNoDriftComm_smul (G : UnitaryMatrix d) (c : ℂ) (X : CMatrix d) :
    finiteNoDriftComm G (c • X) = ‖c‖ * finiteNoDriftComm G X := by
  unfold finiteNoDriftComm
  rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, hsNorm_smul]

theorem finiteNoDriftComm_sum {ι : Type*} (G : UnitaryMatrix d) (s : Finset ι) (X : ι → CMatrix d) :
    finiteNoDriftComm G (∑ i ∈ s, X i) ≤ ∑ i ∈ s, finiteNoDriftComm G (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [finiteNoDriftComm]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (finiteNoDriftComm_add G (X i) (∑ j ∈ s, X j)).trans
      (add_le_add (le_refl (finiteNoDriftComm G (X i))) ih)

theorem finiteNoDriftComm_markov {h : Nat} [NeZero h]
    (G : UnitaryMatrix d) (U : Fin h → UnitaryMatrix d) (X : CMatrix d) {a b : ℝ}
    (hX : finiteNoDriftComm G X ≤ a)
    (hconj : ∀ j, finiteNoDriftComm G (matrixUnitaryConjugation (U j) X) ≤ b ∧
      finiteNoDriftComm G (matrixUnitaryConjugation (U j)⁻¹ X) ≤ b) :
    finiteNoDriftComm G (matrixLazyMarkov U X) ≤ a / 2 + b / 2 := by
  let Y := fun j => matrixUnitaryConjugation (U j) X + matrixUnitaryConjugation (U j)⁻¹ X
  have hy : finiteNoDriftComm G (∑ j, Y j) ≤ (h : ℝ) * (2 * b) := by
    calc
      _ ≤ ∑ j, finiteNoDriftComm G (Y j) := finiteNoDriftComm_sum G Finset.univ Y
      _ ≤ ∑ _j : Fin h, 2 * b := Finset.sum_le_sum (fun j _ => by
        have ht := finiteNoDriftComm_add G (matrixUnitaryConjugation (U j) X) (matrixUnitaryConjugation (U j)⁻¹ X)
        have hj := hconj j
        change finiteNoDriftComm G (Y j) ≤ 2 * b
        linarith)
      _ = _ := by simp
  have ht := finiteNoDriftComm_add G (((1 / 2 : ℝ) : ℂ) • X)
    ((lazyMarkovWeight h : ℂ) • ∑ j, Y j)
  rw [finiteNoDriftComm_smul, finiteNoDriftComm_smul, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (lazyMarkovWeight_nonneg h)] at ht
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at ht
  have hb := mul_le_mul_of_nonneg_left hy (lazyMarkovWeight_nonneg h)
  have hw := lazyMarkovWeight_mul_card h
  have he : lazyMarkovWeight h * ((h : ℝ) * (2 * b)) = b / 2 := by
    calc
      _ = (lazyMarkovWeight h * h) * (2 * b) := by ring
      _ = _ := by rw [hw]; ring
  rw [he] at hb
  rw [matrixLazyMarkov_apply]
  change finiteNoDriftComm G (((1 / 2 : ℝ) : ℂ) • X + (lazyMarkovWeight h : ℂ) • ∑ j, Y j) ≤ _
  linarith

end ThomGame.Analysis
