module

public import ThomGame.Analysis.MatrixALTHighOrthogonality
public import ThomGame.Analysis.MatrixHSRescaling

/-!
# High directions without a normalization premise

Positive scalar rescaling preserves the actual rectangle, eigenvalue,
and orthogonality. Two nonzero high eigenvectors cannot be orthogonal.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat} [NeZero d] {μ : Type*} [Fintype μ]

theorem matrixUCP_no_orthogonal_high_rectangle
    (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ Z, normalizedTrace (F Z) = normalizedTrace Z)
    (E : μ → CMatrix d) (hE : ∀ i, IsStarProjection (E i)) (hne : ∀ i, E i ≠ 0)
    (i j : μ) (X Y : CMatrix d) (hX : X ≠ 0) (hY : Y ≠ 0)
    (hXl : E i * X = X) (hXr : X * E j = X) (hYl : E i * Y = Y) (hYr : Y * E j = Y)
    (lam nu rho : ℝ) (hrho : 0 ≤ rho) (hsmall : rho ≤ 1 / 1024)
    (hsigma : matrixScalarMixingError E F.toLinearMap ≤ rho ^ 4)
    (heX : F X = (lam : ℂ) • X) (heY : F Y = (nu : ℂ) • Y)
    (hhX : 1 - rho ≤ lam) (hhY : 1 - rho ≤ nu) :
    normalizedTrace (star X * Y) ≠ 0 := by
  let M : ℝ := ((max (E i).rank (E j).rank : Nat) : ℝ) / d
  have hM : 0 < M := by
    have hp := matrixProjection_trace_re_pos (hE i) (hne i)
    rw [matrixProjection_trace_eq_rank (hE i)] at hp
    exact hp.trans_le (div_le_div_of_nonneg_right (by exact_mod_cast le_max_left (E i).rank (E j).rank)
      (Nat.cast_nonneg d))
  obtain ⟨a, ha, hXa⟩ := exists_matrixHS_positive_rescaling X hX M hM
  obtain ⟨b, hb, hYb⟩ := exists_matrixHS_positive_rescaling Y hY M hM
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hb' : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have hx : (a : ℂ) • X ≠ 0 := smul_ne_zero ha' hX
  have hy : (b : ℂ) • Y ≠ 0 := smul_ne_zero hb' hY
  have hxL : E i * ((a : ℂ) • X) = (a : ℂ) • X := by rw [mul_smul_comm, hXl]
  have hxR : ((a : ℂ) • X) * E j = (a : ℂ) • X := by rw [smul_mul_assoc, hXr]
  have hyL : E i * ((b : ℂ) • Y) = (b : ℂ) • Y := by rw [mul_smul_comm, hYl]
  have hyR : ((b : ℂ) • Y) * E j = (b : ℂ) • Y := by rw [smul_mul_assoc, hYr]
  have hxE : F ((a : ℂ) • X) = (lam : ℂ) • ((a : ℂ) • X) := by rw [map_smul, heX, smul_comm]
  have hyE : F ((b : ℂ) • Y) = (nu : ℂ) • ((b : ℂ) • Y) := by rw [map_smul, heY, smul_comm]
  have hn := matrixUCP_no_orthogonal_normalized_high_rectangle F hF htrace E hE hne i j
    ((a : ℂ) • X) ((b : ℂ) • Y) hx hy hxL hxR hyL hyR hXa hYb
    lam nu rho hrho hsmall hsigma hxE hyE hhX hhY
  intro hz
  exact hn (by rw [normalizedTrace_pairing_smul, hz, mul_zero])

end ThomGame.Analysis
