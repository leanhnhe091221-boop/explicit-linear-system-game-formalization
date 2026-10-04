module

public import ThomGame.Analysis.MatrixALTHighPolarCompletion

/-!
# Overlap of two partial isometries in the same range corner

The common ambient projection forces a lower bound on the product mass.
No commutation between the two range projections is assumed.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat}

theorem matrixProjection_overlap_trace {P A B : CMatrix d}
    (hP : IsStarProjection P) (hA : IsStarProjection A) (hB : IsStarProjection B)
    (hAP : A ≤ P) (hBP : B ≤ P) :
    (normalizedTrace A).re + (normalizedTrace B).re - (normalizedTrace P).re ≤
      (normalizedTrace (A * B)).re := by
  have hp := (Complex.nonneg_iff.mp (normalizedTrace_mul_nonneg (P - A) (P - B)
    (sub_nonneg.mpr hAP) (sub_nonneg.mpr hBP))).1
  rw [sub_mul, mul_sub, mul_sub, hP.isIdempotentElem.eq,
    (hB.le_iff_mul_eq_right hP).mp hBP, (hA.le_iff_mul_eq_left hP).mp hAP,
    normalizedTrace_sub, normalizedTrace_sub, normalizedTrace_sub, Complex.sub_re, Complex.sub_re,
    Complex.sub_re] at hp
  linarith

theorem hsNorm_star_mul_sq_trace (U V : CMatrix d) :
    hsNorm (star U * V) ^ 2 = (normalizedTrace ((U * star U) * (V * star V))).re := by
  have he := congrArg Complex.re (normalizedTrace_gram (star U * V))
  simp only [star_mul, star_star, Complex.ofReal_re] at he
  rw [mul_assoc (star V), normalizedTrace_mul_comm (star V), mul_assoc] at he
  simpa only [mul_assoc] using he.symm

theorem matrixPartialIsometries_overlap_mass {P U V : CMatrix d}
    (hP : IsStarProjection P) (hU : IsStarProjection (U * star U))
    (hV : IsStarProjection (V * star V)) (hUP : U * star U ≤ P) (hVP : V * star V ≤ P) :
    hsNorm U ^ 2 + hsNorm V ^ 2 - (normalizedTrace P).re ≤ hsNorm (star U * V) ^ 2 := by
  have he := matrixProjection_overlap_trace hP hU hV hUP hVP
  rw [normalizedTrace_mul_comm U, normalizedTrace_mul_comm V,
    normalizedTrace_gram, normalizedTrace_gram, Complex.ofReal_re, Complex.ofReal_re,
    ← hsNorm_star_mul_sq_trace] at he
  exact he

end ThomGame.Analysis
