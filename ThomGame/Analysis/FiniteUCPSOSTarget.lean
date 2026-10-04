module

public import ThomGame.Analysis.FiniteUCPSOSWords
public import ThomGame.Analysis.FiniteNoDriftRecovery
public import ThomGame.Certificates.NetzerThomWordChecker
public import ThomGame.Certificates.NetzerThomNumericBounds
public import ThomGame.Certificates.NetzerThomLifting

/-! Evaluation of the certified target polynomial at the actual shear tuple. -/

@[expose] public section
namespace ThomGame.Analysis
open scoped BigOperators
open ThomGame.Certificates.NetzerThom

variable {d : ℕ}

noncomputable def finiteSOSWordOperator (f : FreeGroup Compressor.Root →* UnitaryMatrix d)
    (w : List ℕ) : Module.End ℂ (CMatrix d) :=
  matrixUnitaryConjugation (f (FreeGroup.mk (ntWord w)))

theorem finiteSOSWordOperator_nil (f : FreeGroup Compressor.Root →* UnitaryMatrix d) :
    finiteSOSWordOperator f [] = 1 := by
  apply LinearMap.ext
  intro X
  simp [finiteSOSWordOperator, ntWord, shearEncodedWord, ← FreeGroup.one_eq_mk]

theorem finiteSOSWordOperator_append (f : FreeGroup Compressor.Root →* UnitaryMatrix d)
    (a b : List ℕ) :
    finiteSOSWordOperator f (a ++ b) = finiteSOSWordOperator f a * finiteSOSWordOperator f b := by
  apply LinearMap.ext
  intro X
  simp only [finiteSOSWordOperator, ntWord, shearEncodedWord, List.map_append,
    ← FreeGroup.mul_mk, map_mul, Module.End.mul_apply]
  exact finiteSOS_conjugation_product _ _ _

noncomputable def finiteSOSPolynomial {R : Type*} [Ring R] [Algebra ℝ R]
    (ρ : List ℕ → R) (p : List (List ℕ × ℤ)) : R :=
  (p.map (fun a => (a.2 : ℝ) • ρ a.1)).sum

theorem finiteSOSPolynomial_mul {R : Type*} [Ring R] [Algebra ℝ R]
    (ρ : List ℕ → R) (hmul : ∀ a b, ρ (a ++ b) = ρ a * ρ b)
    (p q : List (List ℕ × ℤ)) :
    finiteSOSPolynomial ρ (p.flatMap fun a => q.map fun b => (a.1 ++ b.1, a.2 * b.2)) =
      finiteSOSPolynomial ρ p * finiteSOSPolynomial ρ q := by
  induction p with
  | nil => simp [finiteSOSPolynomial]
  | cons a p ih =>
    simp only [List.flatMap_cons, finiteSOSPolynomial, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons, add_mul] at *
    rw [ih]
    congr 1
    clear ih p
    induction q with
    | nil => simp
    | cons b q ihq =>
      simp only [List.map_cons, List.sum_cons, mul_add, Int.cast_mul, hmul]
      rw [ihq]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
      rw [mul_comm (a.2 : ℝ) (b.2 : ℝ)]

theorem finiteSOSPolynomial_scale {R : Type*} [Ring R] [Algebra ℝ R]
    (ρ : List ℕ → R) (p : List (List ℕ × ℤ)) (c : ℤ) :
    finiteSOSPolynomial ρ (p.map (fun a => (a.1, a.2 * c))) =
      (c : ℝ) • finiteSOSPolynomial ρ p := by
  induction p with
  | nil => simp [finiteSOSPolynomial]
  | cons a p ih =>
    simp only [finiteSOSPolynomial, List.map_cons, List.sum_cons, smul_add] at *
    rw [ih, Int.cast_mul, smul_smul, mul_comm (c : ℝ)]

noncomputable def finiteSOSQuadraticFunctional (X : CMatrix d) :
    Module.End ℂ (CMatrix d) →ₗ[ℝ] ℝ where
  toFun T := (normalizedTrace (star X * T X)).re
  map_add' T S := by simp [mul_add]
  map_smul' r T := by
    change (normalizedTrace (star X * ((r : ℂ) • T X))).re = _
    rw [mul_smul_comm, normalizedTrace_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im]
    simp

theorem finiteSOSPolynomial_quadratic (f : FreeGroup Compressor.Root →* UnitaryMatrix d)
    (p : List (List ℕ × ℤ)) (X : CMatrix d) :
    finiteSOSQuadraticFunctional X (finiteSOSPolynomial (finiteSOSWordOperator f) p) =
      (p.map (fun a => (a.2 : ℝ) * finiteSOSQuadratic (f (FreeGroup.mk (ntWord a.1))) X)).sum := by
  unfold finiteSOSPolynomial
  rw [map_list_sum]
  simp only [List.map_map, Function.comp_def, map_smul, smul_eq_mul]
  rfl

theorem finiteSOSPolynomial_target (f : FreeGroup Compressor.Root →* UnitaryMatrix d) :
    (denominator⁻¹ : ℝ) • finiteSOSPolynomial (finiteSOSWordOperator f) targetTerms =
      finiteSOSPolynomial (finiteSOSWordOperator f) laplacianTerms ^ 2 -
        (561 / 2000 : ℝ) • finiteSOSPolynomial (finiteSOSWordOperator f) laplacianTerms := by
  let prod := laplacianTerms.flatMap fun a => laplacianTerms.map fun b => (a.1 ++ b.1, a.2 * b.2)
  have hform : targetTerms =
      prod.map (fun a => (a.1, a.2 * 14641000000000000)) ++
        laplacianTerms.map (fun a => (a.1, a.2 * (-561 * 7320500000000))) := by
    rw [targetTerms_formula]
    simp only [prod, List.map_flatMap, List.map_map, Function.comp_def]
    congr 2
    funext a
    congr 1
    ring
  rw [hform]
  simp only [finiteSOSPolynomial, List.map_append, List.sum_append]
  change denominator⁻¹ • (finiteSOSPolynomial (finiteSOSWordOperator f)
    (prod.map fun a => (a.1, a.2 * 14641000000000000)) +
    finiteSOSPolynomial (finiteSOSWordOperator f)
    (laplacianTerms.map fun a => (a.1, a.2 * (-561 * 7320500000000)))) = _
  rw [finiteSOSPolynomial_scale, finiteSOSPolynomial_scale, smul_add, smul_smul, smul_smul]
  norm_num [denominator, ← sub_eq_add_neg, neg_smul]
  congr 1
  simpa only [pow_two, prod, finiteSOSPolynomial] using finiteSOSPolynomial_mul (finiteSOSWordOperator f)
    (finiteSOSWordOperator_append f) laplacianTerms laplacianTerms

noncomputable def finiteSOSShearTuple (f : FreeGroup Compressor.Root →* UnitaryMatrix d) :
    Fin 6 → UnitaryMatrix d :=
  fun j => f (FreeGroup.of ((Fintype.equivFinOfCardEq Compressor.root_card).symm j))

theorem finiteSOS_sum_roots {M : Type*} [AddCommMonoid M] (F : Compressor.Root → M) :
    (Compressor.roots.map F).sum = ∑ r, F r := by
  have hn : Compressor.roots.Nodup := by decide +kernel
  have hu : Compressor.roots.toFinset = Finset.univ := by
    ext r
    simp [Compressor.mem_roots]
  rw [← List.sum_toFinset F hn, hu]

theorem finiteSOSWordOperator_atoms (f : FreeGroup Compressor.Root →* UnitaryMatrix d) :
    ((List.range 12).map (fun i => finiteSOSWordOperator f [i])).sum =
      (Compressor.roots.map (fun r => matrixUnitaryConjugation (f (FreeGroup.of r)) +
        matrixUnitaryConjugation (f (FreeGroup.of r))⁻¹)).sum := by
  have htrue (r : Compressor.Root) : FreeGroup.mk [(r, true)] = FreeGroup.of r := rfl
  have hfalse (r : Compressor.Root) : FreeGroup.mk [(r, false)] = (FreeGroup.of r)⁻¹ := by
    rw [FreeGroup.of, FreeGroup.inv_mk]
    rfl
  norm_num [List.range_succ, finiteSOSWordOperator, ntWord, shearEncodedWord, ntLetter,
    Compressor.roots, htrue, hfalse]
  abel

theorem finiteSOSPolynomial_laplacian (f : FreeGroup Compressor.Root →* UnitaryMatrix d) :
    finiteSOSPolynomial (finiteSOSWordOperator f) laplacianTerms =
      (24 : ℝ) • (1 - matrixLazyMarkov (finiteSOSShearTuple f)) := by
  have hsum := Equiv.sum_comp (Fintype.equivFinOfCardEq Compressor.root_card).symm
    (fun r => matrixUnitaryConjugation (f (FreeGroup.of r)) +
      matrixUnitaryConjugation (f (FreeGroup.of r))⁻¹)
  have he : finiteSOSPolynomial (finiteSOSWordOperator f) laplacianTerms =
      (12 : ℝ) • (1 : Module.End ℂ (CMatrix d)) -
        ((List.range 12).map (fun i => finiteSOSWordOperator f [i])).sum := by
    simp [finiteSOSPolynomial, laplacianTerms, List.map_map, Function.comp_def,
      finiteSOSWordOperator_nil, sub_eq_add_neg]
    simpa only [List.map_map, Function.comp_def] using
      (List.sum_neg ((List.range 12).map (fun i => finiteSOSWordOperator f [i]))).symm
  rw [he, finiteSOSWordOperator_atoms, finiteSOS_sum_roots, ← hsum]
  unfold matrixLazyMarkov
  change (12 : ℝ) • (1 : Module.End ℂ (CMatrix d)) -
    (∑ j, (matrixUnitaryConjugation (finiteSOSShearTuple f j) +
      matrixUnitaryConjugation (finiteSOSShearTuple f j)⁻¹)) =
    (24 : ℝ) • (1 - ((1 / 2 : ℝ) • (1 : Module.End ℂ (CMatrix d)) +
      lazyMarkovWeight 6 • ∑ j, (matrixUnitaryConjugation (finiteSOSShearTuple f j) +
        matrixUnitaryConjugation (finiteSOSShearTuple f j)⁻¹)))
  norm_num [smul_sub, smul_add, smul_smul, lazyMarkovWeight]
  module

variable [NeZero d]

theorem finiteSOSQuadraticFunctional_markov_defect (U : Fin 6 → UnitaryMatrix d) (X : CMatrix d) :
    finiteSOSQuadraticFunctional X (1 - matrixLazyMarkov U) = matrixCoordinateEnergy U X := by
  exact matrixLazyMarkov_energy U X

theorem finiteSOSQuadraticFunctional_markov_square (U : Fin 6 → UnitaryMatrix d) (X : CMatrix d) :
    finiteSOSQuadraticFunctional X ((1 - matrixLazyMarkov U) ^ 2) =
      hsNorm (X - matrixLazyMarkov U X) ^ 2 := by
  have hp := matrixLazyMarkov_pairing U X (X - matrixLazyMarkov U X)
  have he : normalizedTrace (star (X - matrixLazyMarkov U X) * (X - matrixLazyMarkov U X)) =
      normalizedTrace (star X * ((X - matrixLazyMarkov U X) -
        matrixLazyMarkov U (X - matrixLazyMarkov U X))) := by
    rw [star_sub, sub_mul, normalizedTrace_sub, hp]
    simp only [mul_sub, normalizedTrace_sub]
  change (normalizedTrace (star X * ((X - matrixLazyMarkov U X) -
    matrixLazyMarkov U (X - matrixLazyMarkov U X)))).re = _
  rw [← he, normalizedTrace_gram, Complex.ofReal_re]

theorem finiteSOS_target_quadratic (f : FreeGroup Compressor.Root →* UnitaryMatrix d)
    (X : CMatrix d) :
    ((List.range 182).map (fun i => targetReal i *
      finiteSOSQuadratic (f (FreeGroup.mk (ntWord (targetTerms.getD i ([],0)).1))) X)).sum =
      576 * hsNorm (X - matrixLazyMarkov (finiteSOSShearTuple f) X) ^ 2 -
        (561 / 2000 : ℝ) * (24 * matrixCoordinateEnergy (finiteSOSShearTuple f) X) := by
  have hpoly := congrArg (finiteSOSQuadraticFunctional X) (finiteSOSPolynomial_target f)
  rw [finiteSOSPolynomial_laplacian, smul_pow] at hpoly
  rw [map_sub] at hpoly
  simp only [map_smul] at hpoly
  rw [finiteSOSQuadraticFunctional_markov_square,
    finiteSOSQuadraticFunctional_markov_defect] at hpoly
  norm_num only [smul_eq_mul, show (24 : ℝ) ^ 2 = 576 by norm_num] at hpoly
  rw [finiteSOSPolynomial_quadratic] at hpoly
  have hlist : ((List.range 182).map (fun i => targetReal i *
      finiteSOSQuadratic (f (FreeGroup.mk (ntWord (targetTerms.getD i ([],0)).1))) X)).sum =
      denominator⁻¹ * (targetTerms.map (fun a => (a.2 : ℝ) *
        finiteSOSQuadratic (f (FreeGroup.mk (ntWord a.1))) X)).sum := by
    have hrange {α : Type} (l : List α) (a : α) (F : α → ℝ) :
        ((List.range l.length).map (fun i => F (l.getD i a))).sum = (l.map F).sum := by
      rw [list_range_sum_fin]
      simp only [List.getD_eq_getElem l a (Fin.is_lt _)]
      exact finiteSOS_sum_get l F
    have hh := hrange targetTerms ([],0) (fun a : List ℕ × ℤ => (a.2 : ℝ) *
      finiteSOSQuadratic (f (FreeGroup.mk (ntWord a.1))) X)
    rw [targetTerms_length] at hh
    rw [← hh, ← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [targetReal, div_eq_mul_inv]
    ring
  rw [hlist]
  simpa only [smul_eq_mul, mul_assoc] using hpoly

end ThomGame.Analysis
