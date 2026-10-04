module

public import ThomGame.Analysis.MatrixALTHighIsometry

/-!
# Exact matrix units from isometries with orthogonal final corners

All products are actual ambient matrix products. Multiplication has
the matrix-unit rule when the first two indices share an initial
corner; distinct orthogonal initial corners give zero.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat} {μ : Type*}

theorem matrixSupported_pairing_zero (E U : μ → CMatrix d)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (hleft : ∀ i, E i * U i = U i) {i j : μ} (hij : i ≠ j) : star (U i) * U j = 0 := by
  have hstar : star (U i) * E i = star (U i) := by
    simpa only [star_mul, (hE i).isSelfAdjoint.star_eq] using congrArg star (hleft i)
  calc
    star (U i) * U j = (star (U i) * E i) * (E j * U j) := by rw [hstar, hleft j]
    _ = star (U i) * (E i * E j) * U j := by simp only [mul_assoc]
    _ = 0 := by rw [horth hij, mul_zero, zero_mul]

theorem matrixIsometryUnit_star (U : μ → CMatrix d) (i j : μ) :
    star (U i * star (U j)) = U j * star (U i) := by rw [star_mul, star_star]

theorem matrixIsometryUnit_support (E U : μ → CMatrix d)
    (hE : ∀ i, IsStarProjection (E i)) (hleft : ∀ i, E i * U i = U i) (i j : μ) :
    E i * (U i * star (U j)) = U i * star (U j) ∧
      (U i * star (U j)) * E j = U i * star (U j) := by
  constructor
  · rw [← mul_assoc, hleft i]
  · have hstar : star (U j) * E j = star (U j) := by
      simpa only [star_mul, (hE j).isSelfAdjoint.star_eq] using congrArg star (hleft j)
    rw [mul_assoc, hstar]

theorem matrixIsometryUnit_mul [DecidableEq μ] (E P U : μ → CMatrix d)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (hleft : ∀ i, E i * U i = U i) (hright : ∀ i, U i * P i = U i)
    (hgram : ∀ i, star (U i) * U i = P i) (i j k l : μ) (hij : P i = P j) :
    (U i * star (U j)) * (U k * star (U l)) = if j = k then U i * star (U l) else 0 := by
  by_cases hjk : j = k
  · subst k
    rw [ite_eq_left rfl]
    calc
      (U i * star (U j)) * (U j * star (U l)) = U i * (star (U j) * U j) * star (U l) := by
        simp only [mul_assoc]
      _ = U i * star (U l) := by rw [hgram j, ← hij, hright i]
  · rw [ite_eq_right hjk]
    calc
      (U i * star (U j)) * (U k * star (U l)) = U i * (star (U j) * U k) * star (U l) := by
        simp only [mul_assoc]
      _ = 0 := by rw [matrixSupported_pairing_zero E U hE horth hleft hjk, mul_zero, zero_mul]

theorem matrixIsometryUnit_zero_of_initial_orthogonal {P Q U V : CMatrix d}
    (hQ : IsStarProjection Q) (hU : U * P = U) (hV : V * Q = V) (hPQ : P * Q = 0) :
    U * star V = 0 := by
  have hstar : Q * star V = star V := by
    simpa only [star_mul, hQ.isSelfAdjoint.star_eq] using congrArg star hV
  calc
    U * star V = (U * P) * (Q * star V) := by rw [hU, hstar]
    _ = U * (P * Q) * star V := by simp only [mul_assoc]
    _ = 0 := by rw [hPQ, mul_zero, zero_mul]

theorem matrixIsometryUnit_mass (P U V : CMatrix d)
    (hU : star U * U = P) (hV : star V * V = P) (hVP : V * P = V) :
    hsNorm (U * star V) ^ 2 = (normalizedTrace P).re := by
  have h := congrArg Complex.re (normalizedTrace_gram (U * star V))
  simp only [star_mul, star_star, Complex.ofReal_re] at h
  have he : (V * star U) * (U * star V) = V * star V := by
    calc
      (V * star U) * (U * star V) = V * (star U * U) * star V := by simp only [mul_assoc]
      _ = V * star V := by rw [hU, hVP]
  rw [he, normalizedTrace_mul_comm V, hV] at h
  exact h.symm

theorem matrixIsometryUnit_nonzero [NeZero d] (P U V : CMatrix d)
    (hP : IsStarProjection P) (hne : P ≠ 0)
    (hU : star U * U = P) (hV : star V * V = P) (hVP : V * P = V) : U * star V ≠ 0 := by
  intro hz
  have h := matrixIsometryUnit_mass P U V hU hV hVP
  rw [hz, hsNorm_zero, zero_pow (by decide : (2 : Nat) ≠ 0)] at h
  exact (matrixProjection_trace_re_pos hP hne).ne h

end ThomGame.Analysis
