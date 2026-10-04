module

public import ThomGame.Analysis.MatrixHighDirectionObstruction

/-!
# No two orthogonal high eigenvectors in an actual rectangle

The rank, energy, and distance inputs of the obstruction are all derived
from the actual scalar mixing error and the constructed polar completions.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat} [NeZero d] {μ : Type*} [Fintype μ]

theorem matrixUCP_no_orthogonal_normalized_high_rectangle
    (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ Z, normalizedTrace (F Z) = normalizedTrace Z)
    (E : μ → CMatrix d) (hE : ∀ i, IsStarProjection (E i)) (hne : ∀ i, E i ≠ 0)
    (i j : μ) (X Y : CMatrix d) (hX : X ≠ 0) (hY : Y ≠ 0)
    (hXl : E i * X = X) (hXr : X * E j = X) (hYl : E i * Y = Y) (hYr : Y * E j = Y)
    (hXm : hsNorm X ^ 2 = ((max (E i).rank (E j).rank : Nat) : ℝ) / d)
    (hYm : hsNorm Y ^ 2 = ((max (E i).rank (E j).rank : Nat) : ℝ) / d)
    (lam nu rho : ℝ) (hrho : 0 ≤ rho) (hsmall : rho ≤ 1 / 1024)
    (hsigma : matrixScalarMixingError E F.toLinearMap ≤ rho ^ 4)
    (heX : F X = (lam : ℂ) • X) (heY : F Y = (nu : ℂ) • Y)
    (hhX : 1 - rho ≤ lam) (hhY : 1 - rho ≤ nu) :
    normalizedTrace (star X * Y) ≠ 0 := by
  intro horth
  obtain ⟨U, hUl, hUr, hUi, hUf, hUiQ, hUfP, hUir, hUfr, hUX, hUn, hdU, hfU, hrU, heU⟩ :=
    exists_matrixUCP_high_polar_completion F hF htrace E hE hne i j X hX hXl hXr hXm
      lam rho hrho (by linarith) hsigma heX hhX
  obtain ⟨V, hVl, hVr, hVi, hVf, hViQ, hVfP, hVir, hVfr, hVY, hVn, hdV, hfV, hrV, heV⟩ :=
    exists_matrixUCP_high_polar_completion F hF htrace E hE hne i j Y hY hYl hYr hYm
      nu rho hrho (by linarith) hsigma heY hhY
  let M : ℝ := ((max (E i).rank (E j).rank : Nat) : ℝ) / d
  let t : ℝ := ((min (E i).rank (E j).rank : Nat) : ℝ) / d
  have hM : 0 < M := by
    dsimp only [M]
    rw [← hXm]
    exact sq_pos_of_ne_zero (fun hz => hX ((hsNorm_eq_zero_iff X).mp hz))
  have hUt : hsNorm U ^ 2 = t := by
    have he := congrArg Complex.re (normalizedTrace_gram U)
    rw [matrixProjection_trace_eq_rank hUi, hUir, Complex.ofReal_re] at he
    exact he.symm
  have hVt : hsNorm V ^ 2 = t := by
    have he := congrArg Complex.re (normalizedTrace_gram V)
    rw [matrixProjection_trace_eq_rank hVi, hVir, Complex.ofReal_re] at he
    exact he.symm
  have htM : t ≤ M := div_le_div_of_nonneg_right
    (by exact_mod_cast (min_le_max : min (E i).rank (E j).rank ≤ max (E i).rank (E j).rank))
    (Nat.cast_nonneg d)
  have htQ : t ≤ (normalizedTrace (E j)).re := by
    rw [matrixProjection_trace_eq_rank (hE j)]
    exact div_le_div_of_nonneg_right (by exact_mod_cast min_le_right (E i).rank (E j).rank)
      (Nat.cast_nonneg d)
  have hPM : (normalizedTrace (E i)).re ≤ M := by
    rw [matrixProjection_trace_eq_rank (hE i)]
    exact div_le_div_of_nonneg_right (by exact_mod_cast le_max_left (E i).rank (E j).rank)
      (Nat.cast_nonneg d)
  have hratio : (1 - 2 * rho) * M ≤ t := by
    apply (le_div_iff₀ hM).mp
    change 1 - 2 * rho ≤ (((min (E i).rank (E j).rank : Nat) : ℝ) / d) /
      (((max (E i).rank (E j).rank : Nat) : ℝ) / d)
    rw [div_div_div_cancel_right₀ (Nat.cast_ne_zero.mpr (NeZero.ne d))]
    exact hrU
  have hQM : M / 2 ≤ (normalizedTrace (E j)).re := by
    have he := mul_le_mul_of_nonneg_right (show (1 / 2 : ℝ) ≤ 1 - 2 * rho by linarith) hM.le
    linarith
  have hUs : E j * star U = star U := by
    simpa only [star_mul, (hE j).isSelfAdjoint.star_eq] using congrArg star hUr
  have hc := matrixScalarMixingError_hsNorm_le E F.toLinearMap j (star U * V)
    (by rw [← mul_assoc, hUs]) (by rw [mul_assoc, hVr])
  have hc' : hsNorm (F (star U * V) -
      (normalizedTrace (star U * V) / normalizedTrace (E j)) • E j) ≤ rho ^ 4 * hsNorm (star U * V) :=
    hc.trans (mul_le_mul_of_nonneg_right hsigma (hsNorm_nonneg _))
  rw [hXm] at hdU heU
  rw [hYm] at hdV heV
  exact matrixHighPolar_orthogonality_obstruction F hF htrace (E i) (E j) X Y U V (hE i) (hE j) (hne j)
    rho M hrho hsmall hM hXm.le horth hUf hVf hUfP hVfP hUn hVn
    (hratio.trans_eq hUt.symm) (hratio.trans_eq hVt.symm) (hVt.le.trans htM) hPM hQM hdU hdV heU heV hc'

end ThomGame.Analysis
