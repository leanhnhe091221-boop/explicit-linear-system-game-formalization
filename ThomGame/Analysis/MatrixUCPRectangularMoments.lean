module

public import ThomGame.Analysis.MatrixUCPCornerMoments
public import ThomGame.Analysis.MatrixHermitianEnergyParts
public import ThomGame.Analysis.MatrixProjectionRankTrace

/-!
# Both inequalities in ALT (5.4) for unequal matrix corners

A rectangular eigenvector is normalized to the larger projection trace.
The scalar estimate is applied on that side, while Cauchy--Schwarz is
applied on the smaller side. The resulting ratio is the exact ratio of
the two projection ranks; the ambient normalization cancels.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra

variable {d : Nat} [NeZero d]

theorem matrixUCP_left_corner_fourth_moment (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (P : CMatrix d) (hP : IsStarProjection P) (hne : P ≠ 0) (lam sigma : ℝ)
    (hcorner : ∀ Y : CMatrix d, P * Y = Y → Y * P = Y →
      hsNorm (F Y - (normalizedTrace Y / normalizedTrace P) • P) ≤ sigma * hsNorm Y)
    (X : CMatrix d) (hleft : P * X = X)
    (hmass : normalizedTrace (star X * X) = normalizedTrace P)
    (heigen : F X = (lam : ℂ) • X) :
    (lam ^ 2 - sigma) * hsNorm (star X * X) ^ 2 ≤ hsNorm X ^ 2 := by
  have hr : star X * P = star X := by
    simpa only [star_mul, hP.isSelfAdjoint.star_eq] using congrArg star hleft
  have he : F (star X) = (lam : ℂ) • star X := by
    rw [completelyPositiveMap_star, heigen, star_smul, Complex.star_def, Complex.conj_ofReal]
  have hm : normalizedTrace (star (star X) * star X) = normalizedTrace P := by
    rw [star_star, normalizedTrace_mul_comm]
    exact hmass
  have hb := matrixUCP_corner_fourth_moment F hF P hP hne lam sigma hcorner (star X) hr hm he
  rw [star_star, hsNorm_mul_star_eq_star_mul] at hb
  have hn : hsNorm (star X) = hsNorm X := hsNorm_conjTranspose X
  rw [hn] at hb
  exact hb

theorem matrixUCP_rectangular_moment_bounds (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (P Q : CMatrix d) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hPne : P ≠ 0) (hQne : Q ≠ 0) (lam sigma : ℝ)
    (hcornerP : ∀ Y : CMatrix d, P * Y = Y → Y * P = Y →
      hsNorm (F Y - (normalizedTrace Y / normalizedTrace P) • P) ≤ sigma * hsNorm Y)
    (hcornerQ : ∀ Y : CMatrix d, Q * Y = Y → Y * Q = Y →
      hsNorm (F Y - (normalizedTrace Y / normalizedTrace Q) • Q) ≤ sigma * hsNorm Y)
    (X : CMatrix d) (hX : X ≠ 0) (hleft : P * X = X) (hright : X * Q = X)
    (hnorm : hsNorm X ^ 2 = max (normalizedTrace P).re (normalizedTrace Q).re)
    (heigen : F X = (lam : ℂ) • X) :
    (lam ^ 2 - sigma) * hsNorm (star X * X) ^ 2 ≤
      max (normalizedTrace P).re (normalizedTrace Q).re ∧
    lam ^ 2 - sigma ≤
      min (normalizedTrace P).re (normalizedTrace Q).re / max (normalizedTrace P).re (normalizedTrace Q).re := by
  let M := max (normalizedTrace P).re (normalizedTrace Q).re
  let t := min (normalizedTrace P).re (normalizedTrace Q).re
  let s := hsNorm (star X * X) ^ 2
  have hP₀ : 0 ≤ (normalizedTrace P).re := (Complex.nonneg_iff.mp (normalizedTrace_nonneg P hP.nonneg)).1
  have hQ₀ : 0 ≤ (normalizedTrace Q).re := (Complex.nonneg_iff.mp (normalizedTrace_nonneg Q hQ.nonneg)).1
  have ht₀ : 0 ≤ t := le_min hP₀ hQ₀
  have hM : 0 < M := by
    change 0 < max (normalizedTrace P).re (normalizedTrace Q).re
    rw [← hnorm]
    exact sq_pos_of_ne_zero (fun hz => hX ((hsNorm_eq_zero_iff X).mp hz))
  have hfour : (lam ^ 2 - sigma) * s ≤ M := by
    rcases le_total (normalizedTrace P).re (normalizedTrace Q).re with hpq | hqp
    · have hm : normalizedTrace (star X * X) = normalizedTrace Q := by
        rw [normalizedTrace_gram, hnorm, max_eq_right hpq, normalizedTrace_selfAdjoint_real hQ.isSelfAdjoint]
      exact (matrixUCP_corner_fourth_moment F hF Q hQ hQne lam sigma hcornerQ X hright hm heigen).trans_eq hnorm
    · have hm : normalizedTrace (star X * X) = normalizedTrace P := by
        rw [normalizedTrace_gram, hnorm, max_eq_left hqp, normalizedTrace_selfAdjoint_real hP.isSelfAdjoint]
      exact (matrixUCP_left_corner_fourth_moment F hF P hP hPne lam sigma hcornerP X hleft hm heigen).trans_eq hnorm
  have hcsP : M ^ 2 ≤ (normalizedTrace P).re * s := by
    have hl : P * (X * star X) = X * star X := by rw [← mul_assoc, hleft]
    have hb := matrix_corner_trace_sq_le P (X * star X) hP hl
    rw [normalizedTrace_mul_comm X, normalizedTrace_gram, Complex.ofReal_re,
      hsNorm_mul_star_eq_star_mul, hnorm] at hb
    exact hb
  have hcsQ : M ^ 2 ≤ (normalizedTrace Q).re * s := by
    have hx : Q * star X = star X := by
      simpa only [star_mul, hQ.isSelfAdjoint.star_eq] using congrArg star hright
    have hl : Q * (star X * X) = star X * X := by rw [← mul_assoc, hx]
    have hb := matrix_corner_trace_sq_le Q (star X * X) hQ hl
    rw [normalizedTrace_gram, Complex.ofReal_re, hnorm] at hb
    exact hb
  have hcs : M ^ 2 ≤ t * s := by
    rcases le_total (normalizedTrace P).re (normalizedTrace Q).re with hpq | hqp
    · simpa only [t, min_eq_left hpq] using hcsP
    · simpa only [t, min_eq_right hqp] using hcsQ
  refine ⟨hfour, ?_⟩
  change lam ^ 2 - sigma ≤ t / M
  by_cases hc : 0 ≤ lam ^ 2 - sigma
  · apply (le_div_iff₀ hM).mpr
    have hb := mul_le_mul_of_nonneg_left hcs hc
    have hf := mul_le_mul_of_nonneg_left hfour ht₀
    nlinarith only [hb, hf, hM]
  · exact (le_of_not_ge hc).trans (div_nonneg ht₀ hM.le)

theorem matrixProjection_trace_min_max_ratio (P Q : CMatrix d)
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    min (normalizedTrace P).re (normalizedTrace Q).re / max (normalizedTrace P).re (normalizedTrace Q).re =
      ((min P.rank Q.rank : Nat) : ℝ) / ((max P.rank Q.rank : Nat) : ℝ) := by
  rw [matrixProjection_trace_eq_rank hP, matrixProjection_trace_eq_rank hQ,
    min_div_div_right (Nat.cast_nonneg d), max_div_div_right (Nat.cast_nonneg d),
    div_div_div_cancel_right₀ (Nat.cast_ne_zero.mpr (NeZero.ne d)), Nat.cast_min, Nat.cast_max]

theorem matrixUCP_rectangular_ALT_5_4 (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (P Q : CMatrix d) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hPne : P ≠ 0) (hQne : Q ≠ 0) (lam sigma : ℝ)
    (hcornerP : ∀ Y : CMatrix d, P * Y = Y → Y * P = Y →
      hsNorm (F Y - (normalizedTrace Y / normalizedTrace P) • P) ≤ sigma * hsNorm Y)
    (hcornerQ : ∀ Y : CMatrix d, Q * Y = Y → Y * Q = Y →
      hsNorm (F Y - (normalizedTrace Y / normalizedTrace Q) • Q) ≤ sigma * hsNorm Y)
    (X : CMatrix d) (hX : X ≠ 0) (hleft : P * X = X) (hright : X * Q = X)
    (hnorm : hsNorm X ^ 2 = ((max P.rank Q.rank : Nat) : ℝ) / d)
    (heigen : F X = (lam : ℂ) • X) :
    (lam ^ 2 - sigma) * (Matrix.trace ((star X * X) ^ 2)).re ≤ ((max P.rank Q.rank : Nat) : ℝ) ∧
    lam ^ 2 - sigma ≤ ((min P.rank Q.rank : Nat) : ℝ) / ((max P.rank Q.rank : Nat) : ℝ) := by
  have hM : max (normalizedTrace P).re (normalizedTrace Q).re = ((max P.rank Q.rank : Nat) : ℝ) / d := by
    rw [matrixProjection_trace_eq_rank hP, matrixProjection_trace_eq_rank hQ,
      max_div_div_right (Nat.cast_nonneg d), Nat.cast_max]
  obtain ⟨hfour, hratio⟩ := matrixUCP_rectangular_moment_bounds F hF P Q hP hQ hPne hQne lam sigma
    hcornerP hcornerQ X hX hleft hright (hnorm.trans hM.symm) heigen
  rw [matrixProjection_trace_min_max_ratio P Q hP hQ] at hratio
  refine ⟨?_, hratio⟩
  have ht := congrArg Complex.re (normalizedTrace_gram (star X * X))
  rw [(star_mul_self_nonneg X).isSelfAdjoint.star_eq, ← sq, normalizedTrace_re, Complex.ofReal_re] at ht
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have ht' := (div_eq_iff hd.ne').mp ht
  rw [hM] at hfour
  have hb := (le_div_iff₀ hd).mp hfour
  rw [ht']
  nlinarith only [hb]

end ThomGame.Analysis
