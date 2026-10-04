module

public import ThomGame.Analysis.MatrixReducingFrame

/-!
# Every matrix in a rank-one corner is scalar

An actual frame from the one-dimensional matrix algebra proves the
scalar formula, with the normalized trace of the original ambient
matrix algebra. It gives arbitrary scalar gap on every rank-one block.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d h : Nat}

theorem matrixRankOneCorner_exists_scalar {P : CMatrix d} (hP : IsStarProjection P)
    (hrank : P.rank = 1) (X : CMatrix d) (hleft : P * X = X) (hright : X * P = X) :
    ∃ c : ℂ, X = c • P := by
  obtain ⟨F, hFi, hFf⟩ := exists_matrixPartialIsometry_of_rank_eq
    (IsStarProjection.one (R := CMatrix 1)) hP (by simp only [Matrix.rank_one, Fintype.card_fin, hrank])
  let Y : CMatrix 1 := Fᴴ * X * F
  have hY : Y = Y 0 0 • (1 : CMatrix 1) := by
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst i
    subst j
    simp
  have hX : matrixFrameLift F Y = X := by
    rw [matrixFrameLift_compression, hFf, hleft, hright]
  refine ⟨Y 0 0, ?_⟩
  calc
    X = matrixFrameLift F Y := hX.symm
    _ = matrixFrameLift F (Y 0 0 • 1) := congrArg (matrixFrameLift F) hY
    _ = Y 0 0 • P := by rw [matrixFrameLift_smul, matrixFrameLift_one, hFf]

theorem normalizedTrace_projection_ne_zero [NeZero d] {P : CMatrix d}
    (hP : IsStarProjection P) (hne : P ≠ 0) : normalizedTrace P ≠ 0 := by
  intro hz
  have hp := matrixTraceReal_projection_pos (NeZero.pos d) hP hne
  have he := congrArg Complex.re hz
  have he' : matrixTraceReal d P = 0 := by
    simpa only [normalizedTrace_re, matrixTraceReal, Complex.zero_re] using he
  linarith only [hp, he']

theorem matrixRankOneCorner_eq_trace_scalar [NeZero d] {P : CMatrix d} (hP : IsStarProjection P)
    (hrank : P.rank = 1) (X : CMatrix d) (hleft : P * X = X) (hright : X * P = X) :
    X = (normalizedTrace X / normalizedTrace P) • P := by
  obtain ⟨c, hc⟩ := matrixRankOneCorner_exists_scalar hP hrank X hleft hright
  have hne : P ≠ 0 := by intro hz; simp only [hz, Matrix.rank_zero] at hrank; omega
  have htr := normalizedTrace_projection_ne_zero hP hne
  rw [hc, normalizedTrace_smul, mul_div_cancel_right₀ c htr]

theorem matrixRankOneCorner_scalar_gap [NeZero d] (U : Fin h → UnitaryMatrix d) (c : ℝ)
    {P : CMatrix d} (hP : IsStarProjection P) (hrank : P.rank = 1)
    (X : CMatrix d) (hleft : P * X = X) (hright : X * P = X) :
    c * hsNorm (X - (normalizedTrace X / normalizedTrace P) • P) ^ 2 ≤ matrixCoordinateEnergy U X := by
  have he : X - (normalizedTrace X / normalizedTrace P) • P = 0 :=
    sub_eq_zero.mpr (matrixRankOneCorner_eq_trace_scalar hP hrank X hleft hright)
  rw [he, hsNorm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
  exact matrixCoordinateEnergy_nonneg U X

end ThomGame.Analysis
