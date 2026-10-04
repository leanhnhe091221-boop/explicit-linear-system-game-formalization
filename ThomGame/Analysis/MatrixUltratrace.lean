module

public import ThomGame.Analysis.MatrixSequenceTrace

/-!
# A faithful normalized trace on the actual matrix star-algebra quotient

The normalized ultralimit descends through the 2-null ideal. Positivity
and faithfulness follow from the finite-dimensional Gram trace formula.
This is an algebraic tracial star algebra; no operator-topology completeness
or von Neumann algebra realization is asserted here.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable {ι : Type*} (dims : ι → Nat) (hd : ∀ i, 0 < dims i) (U : Ultrafilter ι)

noncomputable def matrixUltratrace : MatrixTracialQuotient dims (U : Filter ι) → ℂ :=
  Quotient.lift (matrixSequenceUltratrace dims U) (by
    intro A B h
    exact matrixSequenceUltratrace_eq_of_null_sub dims hd U A B
      ((Submodule.quotientRel_def _).mp h))

@[simp] theorem matrixUltratrace_mk (A : BoundedMatrixSequence dims) :
    matrixUltratrace dims hd U (matrixQuotientMk dims (U : Filter ι) A) =
      matrixSequenceUltratrace dims U A := rfl

@[simp] theorem matrixUltratrace_zero : matrixUltratrace dims hd U 0 = 0 := by
  exact matrixSequenceUltratrace_zero dims hd U

@[simp] theorem matrixUltratrace_one : matrixUltratrace dims hd U 1 = 1 := by
  exact matrixSequenceUltratrace_one dims hd U

theorem matrixUltratrace_add (x y : MatrixTracialQuotient dims (U : Filter ι)) :
    matrixUltratrace dims hd U (x + y) = matrixUltratrace dims hd U x + matrixUltratrace dims hd U y := by
  obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims (U : Filter ι) x
  obtain ⟨B, rfl⟩ := matrixQuotientMk_surjective dims (U : Filter ι) y
  rw [← map_add]
  exact matrixSequenceUltratrace_add dims hd U A B

theorem matrixUltratrace_smul (c : ℂ) (x : MatrixTracialQuotient dims (U : Filter ι)) :
    matrixUltratrace dims hd U (c • x) = c * matrixUltratrace dims hd U x := by
  obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims (U : Filter ι) x
  exact matrixSequenceUltratrace_smul dims hd U c A

noncomputable def matrixUltratraceLinear : MatrixTracialQuotient dims (U : Filter ι) →ₗ[ℂ] ℂ where
  toFun := matrixUltratrace dims hd U
  map_add' := matrixUltratrace_add dims hd U
  map_smul' := matrixUltratrace_smul dims hd U

theorem matrixUltratrace_star (x : MatrixTracialQuotient dims (U : Filter ι)) :
    matrixUltratrace dims hd U (star x) = star (matrixUltratrace dims hd U x) := by
  obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims (U : Filter ι) x
  exact matrixSequenceUltratrace_star dims hd U A

theorem matrixUltratrace_mul_comm (x y : MatrixTracialQuotient dims (U : Filter ι)) :
    matrixUltratrace dims hd U (x * y) = matrixUltratrace dims hd U (y * x) := by
  obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims (U : Filter ι) x
  obtain ⟨B, rfl⟩ := matrixQuotientMk_surjective dims (U : Filter ι) y
  rw [← map_mul, ← map_mul]
  exact matrixSequenceUltratrace_mul_comm dims hd U A B

theorem matrixUltratrace_gram_tendsto (A : BoundedMatrixSequence dims) :
    Tendsto (fun i => (hsNorm (A.val i) ^ 2 : ℂ)) (U : Filter ι)
      (𝓝 (matrixUltratrace dims hd U
        (star (matrixQuotientMk dims (U : Filter ι) A) * matrixQuotientMk dims (U : Filter ι) A))) := by
  rw [matrixQuotientMk_star, ← map_mul, matrixUltratrace_mk]
  have h := matrixSequenceUltratrace_tendsto dims hd U (star A * A)
  change Tendsto (fun i => normalizedTrace (star (A.val i) * A.val i)) _ _ at h
  simpa only [normalizedTrace_gram, Complex.ofReal_pow] using h

theorem matrixUltratrace_gram_nonneg (x : MatrixTracialQuotient dims (U : Filter ι)) :
    0 ≤ (matrixUltratrace dims hd U (star x * x)).re := by
  obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims (U : Filter ι) x
  apply ge_of_tendsto' (Complex.continuous_re.continuousAt.tendsto.comp
    (matrixUltratrace_gram_tendsto dims hd U A))
  intro i
  simp only [Function.comp_def, ← Complex.ofReal_pow, Complex.ofReal_re]
  exact sq_nonneg _

theorem matrixUltratrace_gram_im (x : MatrixTracialQuotient dims (U : Filter ι)) :
    (matrixUltratrace dims hd U (star x * x)).im = 0 := by
  obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims (U : Filter ι) x
  apply tendsto_nhds_unique (Complex.continuous_im.continuousAt.tendsto.comp
    (matrixUltratrace_gram_tendsto dims hd U A))
  simpa only [Function.comp_def, ← Complex.ofReal_pow, Complex.ofReal_im] using
    (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : ℝ)) (U : Filter ι) (𝓝 0))

theorem matrixUltratrace_faithful (x : MatrixTracialQuotient dims (U : Filter ι)) :
    matrixUltratrace dims hd U (star x * x) = 0 ↔ x = 0 := by
  constructor
  · intro hx
    obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims (U : Filter ι) x
    apply (matrixQuotientMk_eq_zero_iff dims (U : Filter ι) A).mpr
    have h := Complex.continuous_re.continuousAt.tendsto.comp
      (matrixUltratrace_gram_tendsto dims hd U A)
    rw [hx] at h
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp h
    simpa only [Function.comp_def, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.zero_re,
      Real.sqrt_sq (hsNorm_nonneg _), Real.sqrt_zero] using hs
  · rintro rfl
    simp only [star_zero, mul_zero, matrixUltratrace_zero]

end ThomGame.Analysis
