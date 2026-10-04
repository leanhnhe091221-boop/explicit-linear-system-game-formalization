module

public import ThomGame.Analysis.MatrixCheeger
public import ThomGame.Analysis.MatrixReducingFrame

/-!
# Cheeger inequality on an actual nonzero reducing corner

A rank-sized orthonormal frame gives the smaller matrix algebra.
Its normalized trace, squared HS norm and energy are transported
back together, so the final statement uses the original ambient norm.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d h : Nat} [NeZero d] [NeZero h]

theorem matrixCoordinateEnergy_corner_cheeger (U : Fin h → UnitaryMatrix d)
    {P : CMatrix d} (hP : IsStarProjection P) (hPne : P ≠ 0)
    (hred : ∀ j, Commute P (U j).val) {α : ℝ} (hα : 0 ≤ α)
    (hexpand : ∀ p : CMatrix d, IsStarProjection p → p ≤ P → 2 * p.rank ≤ P.rank →
      α * matrixTraceReal d p ≤ matrixCoordinateEnergy U p)
    (X : CMatrix d) (hleft : P * X = X) (hright : X * P = X) :
    α ^ 2 * hsNorm (X - (normalizedTrace X / normalizedTrace P) • P) ^ 2 ≤ matrixCoordinateEnergy U X := by
  classical
  have hnpos := matrixProjection_rank_pos hP hPne
  let : NeZero P.rank := ⟨ne_of_gt hnpos⟩
  obtain ⟨F, hFi, hFf⟩ := exists_matrixPartialIsometry_of_rank_eq
    (IsStarProjection.one (R := CMatrix P.rank)) hP (by simp)
  choose V hV using fun j => exists_matrixFrameReducingUnitary hP hFi hFf (U j) (hred j)
  have hscale : 0 < (P.rank : ℝ) / d := div_pos (Nat.cast_pos.mpr hnpos) (Nat.cast_pos.mpr (NeZero.pos d))
  have hcut (p : CMatrix P.rank) (hp : IsStarProjection p) (hr : 2 * p.rank ≤ P.rank) :
      α * matrixTraceReal P.rank p ≤ matrixCoordinateEnergy V p := by
    have hh := hexpand (matrixFrameLift F p) (matrixFrameLift_isStarProjection hFi hp)
      (matrixFrameLift_projection_le hP hFi hFf hp) (by rwa [matrixFrameLift_projection_rank hFi hp])
    rw [matrixTraceReal_frameLift_scale hFi,
      matrixCoordinateEnergy_frameLift hFi hFf U V hred hV] at hh
    apply (mul_le_mul_iff_right₀ hscale).mp
    convert hh using 1
    ring
  let Y : CMatrix P.rank := Fᴴ * X * F
  have hY : matrixFrameLift F Y = X := by
    rw [matrixFrameLift_compression, hFf, hleft, hright]
  have htraceP : normalizedTrace P = (P.rank : ℂ) / d := by
    have ht := normalizedTrace_frameLift_scale hFi (1 : CMatrix P.rank)
    rwa [matrixFrameLift_one, hFf, normalizedTrace_one, mul_one] at ht
  have htraceX : normalizedTrace X = (P.rank : ℂ) / d * normalizedTrace Y :=
    (congrArg normalizedTrace hY).symm.trans (normalizedTrace_frameLift_scale hFi Y)
  have hratio : normalizedTrace X / normalizedTrace P = normalizedTrace Y := by
    rw [htraceX, htraceP]
    have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
    have hn : (P.rank : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hnpos)
    field_simp
  have he : matrixFrameLift F (Y - normalizedTrace Y • 1) =
      X - (normalizedTrace X / normalizedTrace P) • P := by
    rw [matrixFrameLift_sub, matrixFrameLift_smul, matrixFrameLift_one, hFf, hY, hratio]
  have hh := mul_le_mul_of_nonneg_left (matrixCoordinateEnergy_cheeger V hα hcut Y) hscale.le
  rw [← he, hsNorm_frameLift_sq hFi, ← hY,
    matrixCoordinateEnergy_frameLift hFi hFf U V hred hV]
  convert hh using 1
  ring

end ThomGame.Analysis
