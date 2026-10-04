module

public import ThomGame.Analysis.FiniteUCPSOSBounds
public import ThomGame.Analysis.FiniteNoDriftWords

/-! Matrix quadratic forms and short-word estimates used by the finite SOS
certificate. Relator error is measured in the original normalized HS norm. -/

@[expose] public section
namespace ThomGame.Analysis
open scoped BigOperators Matrix.Norms.L2Operator

variable {d : ℕ}

noncomputable def finiteSOSQuadratic (U : UnitaryMatrix d) (X : CMatrix d) : ℝ :=
  (normalizedTrace (star X * matrixUnitaryConjugation U X)).re

theorem finiteSOSQuadratic_one (X : CMatrix d) : finiteSOSQuadratic 1 X = hsNorm X ^ 2 := by
  simp [finiteSOSQuadratic, matrixUnitaryConjugation_apply, normalizedTrace_gram]
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

theorem finiteSOS_conjugation_product (U V : UnitaryMatrix d) (X : CMatrix d) :
    matrixUnitaryConjugation (U * V) X = matrixUnitaryConjugation U (matrixUnitaryConjugation V X) := by
  simp only [matrixUnitaryConjugation_apply, Matrix.UnitaryGroup.mul_val, star_mul, mul_assoc]

variable [NeZero d]

theorem finiteSOSQuadratic_sub_le (U V : UnitaryMatrix d) (X : CMatrix d)
    (hX : matrixOpNorm X ≤ 1) :
    |finiteSOSQuadratic U X - finiteSOSQuadratic V X| ≤ 2 * unitaryDist U V := by
  let Y := matrixUnitaryConjugation U X - matrixUnitaryConjugation V X
  have he : finiteSOSQuadratic U X - finiteSOSQuadratic V X =
      (inner ℂ (finiteMatrixHilbertEquiv d X) (finiteMatrixHilbertEquiv d Y)).re := by
    rw [finiteMatrixHilbert_inner]
    simp only [Y, finiteSOSQuadratic, mul_sub, normalizedTrace_sub, Complex.sub_re]
  have hc := (Complex.abs_re_le_norm
    (inner ℂ (finiteMatrixHilbertEquiv d X) (finiteMatrixHilbertEquiv d Y))).trans
    (norm_inner_le_norm (𝕜 := ℂ) (finiteMatrixHilbertEquiv d X) (finiteMatrixHilbertEquiv d Y))
  rw [finiteMatrixHilbert_norm, finiteMatrixHilbert_norm] at hc
  have hx := (hsNorm_le_matrixOpNorm X).trans hX
  have hh : hsNorm X * hsNorm Y ≤ hsNorm Y := mul_le_of_le_one_left (hsNorm_nonneg Y) hx
  have hy := matrixUnitaryConjugation_sub_le U V X
  change hsNorm Y ≤ 2 * unitaryDist U V * matrixOpNorm X at hy
  have hy' := hy.trans (mul_le_of_le_one_right
    (mul_nonneg (by norm_num) (unitaryDist_nonneg U V)) hX)
  rw [he]
  exact hc.trans (hh.trans hy')

theorem finiteSOS_relator_quadratic_transfer {G : Type*} [Group G]
    {rels : Set G} {u v : G} {area : ℕ}
    (heq : RelatorEquality rels u v area) (f : G →* UnitaryMatrix d)
    {δ : ℝ} (hδ : 0 ≤ δ) (hf : ∀ r ∈ rels, unitaryLength (f r) ≤ δ)
    (X : CMatrix d) (hX : matrixOpNorm X ≤ 1) :
    |finiteSOSQuadratic (f u) X - finiteSOSQuadratic (f v) X| ≤ 2 * (area : ℝ) * δ := by
  have hd := heq.unitaryDist_le f hδ hf
  exact (finiteSOSQuadratic_sub_le (f u) (f v) X hX).trans (by nlinarith)

theorem finiteSOSQuadratic_gram_pair (U V : UnitaryMatrix d) (X : CMatrix d) :
    finiteSOSQuadratic (U⁻¹ * V) X =
      (inner ℂ (finiteMatrixHilbertEquiv d (matrixUnitaryConjugation U X))
        (finiteMatrixHilbertEquiv d (matrixUnitaryConjugation V X))).re := by
  rw [finiteMatrixHilbert_inner, matrixUnitaryConjugation_pairing]
  unfold finiteSOSQuadratic
  rw [finiteSOS_conjugation_product]

theorem finiteSOSQuadratic_gram_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → κ → ℝ) (U : ι → UnitaryMatrix d) (X : CMatrix d) :
    0 ≤ ∑ i, ∑ j, (∑ k, c i k * c j k) * finiteSOSQuadratic ((U i)⁻¹ * U j) X := by
  let : InnerProductSpace ℝ (FiniteMatrixHilbert d) := InnerProductSpace.complexToReal
  have hh := finiteSOS_gram_nonneg c (fun i => finiteMatrixHilbertEquiv d (matrixUnitaryConjugation (U i) X))
  simpa only [finiteSOSQuadratic_gram_pair, real_inner_eq_re_inner, RCLike.re_to_complex] using hh

omit [NeZero d] in
theorem finiteSOS_word_displacement_sq {S : Type*} (f : S → UnitaryMatrix d)
    (w : Word S) (X : CMatrix d) {D : ℝ} (hD : 0 ≤ D) (hlen : w.length ≤ 4)
    (hcomm : ∀ g b, (g, b) ∈ w → finiteNoDriftComm (f g) X ^ 2 ≤ D) :
    hsNorm (X - matrixUnitaryConjugation (Word.eval f w) X) ^ 2 ≤ 16 * D := by
  have hw := finiteNoDrift_word_comm f w X
    (fun g b hg => Real.le_sqrt_of_sq_le (hcomm g b hg))
  have hlenR : (w.length : ℝ) ≤ 4 := by exact_mod_cast hlen
  have hh := hw.trans (mul_le_mul_of_nonneg_right hlenR (Real.sqrt_nonneg D))
  have hs := pow_le_pow_left₀ (finiteNoDriftComm_nonneg (Word.eval f w) X) hh 2
  rw [hsNorm_sub_comm, matrixUnitaryConjugation_sub_hsNorm]
  change finiteNoDriftComm (Word.eval f w) X ^ 2 ≤ _
  simpa only [mul_pow, Real.sq_sqrt hD, show (4 : ℝ) ^ 2 = 16 by norm_num] using hs

theorem finiteSOS_matrix_residual_bound_list {ι S : Type*}
    (l : List ι) (c : ι → ℝ) (w : ι → Word S) (f : S → UnitaryMatrix d)
    (X : CMatrix d) {D mass : ℝ} (hD : 0 ≤ D)
    (hsum : (l.map c).sum = 0) (hmass : (l.map (fun i => |c i|)).sum ≤ mass)
    (hlen : ∀ i ∈ l, (w i).length ≤ 4)
    (hcomm : ∀ i ∈ l, ∀ g b, (g, b) ∈ w i → finiteNoDriftComm (f g) X ^ 2 ≤ D) :
    -(4 * mass * D) ≤ (l.map (fun i => c i * finiteSOSQuadratic (Word.eval f (w i)) X)).sum := by
  let : InnerProductSpace ℝ (FiniteMatrixHilbert d) := InnerProductSpace.complexToReal
  have hh := finiteSOS_residual_bound_list l c (finiteMatrixHilbertEquiv d X)
    (fun i => finiteMatrixHilbertEquiv d (matrixUnitaryConjugation (Word.eval f (w i)) X))
    hD hsum hmass
    (fun i _ => by simp only [finiteMatrixHilbert_norm, matrixUnitaryConjugation_hsNorm])
    (fun i hi => by
      rw [← map_sub, finiteMatrixHilbert_norm]
      exact finiteSOS_word_displacement_sq f (w i) X hD (hlen i hi) (hcomm i hi))
  simpa only [real_inner_eq_re_inner, RCLike.re_to_complex, finiteMatrixHilbert_inner, finiteSOSQuadratic] using hh

end ThomGame.Analysis
