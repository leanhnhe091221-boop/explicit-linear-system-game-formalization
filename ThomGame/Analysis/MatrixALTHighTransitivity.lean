module

public import ThomGame.Analysis.MatrixALTRectangleApproximation
public import ThomGame.Analysis.MatrixRectangleFixedError
public import ThomGame.Analysis.HighRelationNumerics

/-!
# Transitivity of the actual high-eigenvalue relation

The two genuine polar completions have a product with large overlap
mass and small fixing error. The low spectral branch is impossible.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat} [NeZero d]

theorem matrixUCP_high_rectangle_trans {μ : Type*} [Fintype μ]
    (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ Z, normalizedTrace (F Z) = normalizedTrace Z)
    (hpair : ∀ X Y, normalizedTrace (star (F X) * Y) = normalizedTrace (star X * F Y))
    (E : μ → CMatrix d) (hE : ∀ i, IsStarProjection (E i)) (hne : ∀ i, E i ≠ 0)
    (i j k : μ)
    (hinv : ∀ a b, ∀ X ∈ matrixRectangleSubmodule (E a) (E b),
      F X ∈ matrixRectangleSubmodule (E a) (E b))
    (rho : ℝ) (hrho : 0 ≤ rho) (hsmall : rho ≤ 1 / 1024)
    (hsigma : matrixScalarMixingError E F.toLinearMap ≤ rho ^ 4)
    (hbandsij : ∀ (lam : ℝ) (X : CMatrix d), X ≠ 0 → E i * X = X → X * E j = X →
      F X = (lam : ℂ) • X → (-rho ≤ lam ∧ lam ≤ rho) ∨ (1 - rho ≤ lam ∧ lam ≤ 1))
    (hbandsjk : ∀ (lam : ℝ) (X : CMatrix d), X ≠ 0 → E j * X = X → X * E k = X →
      F X = (lam : ℂ) • X → (-rho ≤ lam ∧ lam ≤ rho) ∨ (1 - rho ≤ lam ∧ lam ≤ 1))
    (hbandsik : ∀ (lam : ℝ) (X : CMatrix d), X ≠ 0 → E i * X = X → X * E k = X →
      F X = (lam : ℂ) • X → (-rho ≤ lam ∧ lam ≤ rho) ∨ (1 - rho ≤ lam ∧ lam ≤ 1))
    (hij : matrixRectangleHasHighEigenvalue F.toLinearMap (E i) (E j) rho)
    (hjk : matrixRectangleHasHighEigenvalue F.toLinearMap (E j) (E k) rho) :
    matrixRectangleHasHighEigenvalue F.toLinearMap (E i) (E k) rho := by
  obtain ⟨U, hUl, hUr, _, hUi, _, hUiQ, _, hUir, _, hUn, heU, hrU, _⟩ :=
    exists_matrixUCP_high_rectangle_approximation F hF htrace hpair E hE hne i j (hinv i j)
      rho hrho hsmall hsigma hbandsij hij
  obtain ⟨V, hVl, hVr, _, hVi, hVf, _, hVfP, hVir, _, hVn, heV, hrV, _⟩ :=
    exists_matrixUCP_high_rectangle_approximation F hF htrace hpair E hE hne j k (hinv j k)
      rho hrho hsmall hsigma hbandsjk hjk
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hpos a : (0 : ℝ) < (E a).rank := by
    have h := matrixProjection_trace_re_pos (hE a) (hne a)
    rw [matrixProjection_trace_eq_rank (hE a)] at h
    exact (div_pos_iff.mp h).resolve_right (fun h => (not_lt_of_ge hd.le) h.2) |>.1
  have hmaxij : (0 : ℝ) < ((max (E i).rank (E j).rank : Nat) : ℝ) :=
    (hpos i).trans_le (Nat.cast_le.mpr (le_max_left _ _))
  have hmaxjk : (0 : ℝ) < ((max (E j).rank (E k).rank : Nat) : ℝ) :=
    (hpos j).trans_le (Nat.cast_le.mpr (le_max_left _ _))
  have hrU' := (le_div_iff₀ hmaxij).mp hrU
  have hrV' := (le_div_iff₀ hmaxjk).mp hrV
  simp only [Nat.cast_max, Nat.cast_min] at hrU' hrV'
  have hover := highRelation_triple_overlap ((E i).rank : ℝ) ((E j).rank : ℝ)
    ((E k).rank : ℝ) rho hrho hrU' hrV'
  let M : ℝ := ((max (max (E i).rank (E j).rank) (E k).rank : Nat) : ℝ) / d
  have hM : 0 < M := div_pos ((hpos i).trans_le
    (Nat.cast_le.mpr ((le_max_left _ _).trans (le_max_left _ _)))) hd
  have hmU : hsNorm U ^ 2 = ((min (E i).rank (E j).rank : Nat) : ℝ) / d := by
    have h := congrArg Complex.re (normalizedTrace_gram U)
    rw [Complex.ofReal_re, matrixProjection_trace_eq_rank hUi, hUir] at h
    exact h.symm
  have hmV : hsNorm V ^ 2 = ((min (E j).rank (E k).rank : Nat) : ℝ) / d := by
    have h := congrArg Complex.re (normalizedTrace_gram V)
    rw [Complex.ofReal_re, matrixProjection_trace_eq_rank hVi, hVir] at h
    exact h.symm
  have hmass : (1 - 4 * rho) * M ≤ hsNorm (U * V) ^ 2 := by
    have h := matrixPartialIsometries_overlap_mass (U := star U) (V := V) (hE j)
      (by simpa only [star_star] using hUi) hVf (by simpa only [star_star] using hUiQ) hVfP
    rw [star_star, Matrix.star_eq_conjTranspose, hsNorm_conjTranspose, hmU, hmV,
      matrixProjection_trace_eq_rank (hE j)] at h
    have hn := div_le_div_of_nonneg_right hover hd.le
    simp only [← Nat.cast_max, ← Nat.cast_min] at hn
    dsimp only [M]
    calc
      (1 - 4 * rho) * (((max (max (E i).rank (E j).rank) (E k).rank : Nat) : ℝ) / d) =
          ((1 - 4 * rho) * ((max (max (E i).rank (E j).rank) (E k).rank : Nat) : ℝ)) / d := by ring
      _ ≤ (((min (E i).rank (E j).rank : Nat) : ℝ) +
          ((min (E j).rank (E k).rank : Nat) : ℝ) - ((E j).rank : ℝ)) / d := hn
      _ = _ := by rw [sub_div, add_div]
      _ ≤ _ := h
  have hmaxU : (((max (E i).rank (E j).rank : Nat) : ℝ) / d) ≤ M :=
    div_le_div_of_nonneg_right (Nat.cast_le.mpr (le_max_left _ _)) hd.le
  have hmaxV : (((max (E j).rank (E k).rank : Nat) : ℝ) / d) ≤ M :=
    div_le_div_of_nonneg_right (Nat.cast_le.mpr (max_le
      ((le_max_right _ _).trans (le_max_left _ _)) (le_max_right _ _))) hd.le
  have heU' := heU.trans (mul_le_mul_of_nonneg_left hmaxU (by positivity : 0 ≤ 18 * rho))
  have heV' := heV.trans (mul_le_mul_of_nonneg_left hmaxV (by positivity : 0 ≤ 18 * rho))
  have herr := matrixUCP_product_fixed_error_sq F hF htrace U V hUn hVn
  have herr' : hsNorm (F (U * V) - U * V) ^ 2 ≤ 144 * rho * M := by linarith
  by_contra hno
  have hlow := matrixUCP_no_high_rectangle_norm_le F hF htrace hpair (E i) (E k)
    (hinv i k) rho hrho hbandsik hno
  have hUlV : E i * (U * V) = U * V := by rw [← mul_assoc, hUl]
  have hUVr : (U * V) * E k = U * V := by rw [mul_assoc, hVr]
  have hlower := matrixRectangle_fixed_error_lower F.toLinearMap (E i) (E k) (hinv i k)
    rho hlow (U * V) hUlV hUVr
  exact highRelation_low_product_impossible rho M (hsNorm (U * V)) (hsNorm (F (U * V) - U * V))
    hsmall hM (hsNorm_nonneg _) (hsNorm_nonneg _) hmass herr' hlower

end ThomGame.Analysis
