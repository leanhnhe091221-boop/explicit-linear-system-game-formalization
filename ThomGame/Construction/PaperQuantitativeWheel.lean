module

public import ThomGame.Construction.PaperGame
public import ThomGame.Analysis.SolutionWheelArea
public import ThomGame.Analysis.QuantitativeInvolutionSubstitution
public import ThomGame.Analysis.QuantitativeWordNormalization
public import ThomGame.Analysis.QuantitativeSolutionReindex
public import ThomGame.Analysis.PaperSolutionApproximation

/-! Quantitative transport through the actual numbered wheel system. All constants
are explicit; the uniform word bound uses the existing total-length certificate. -/

@[expose] public section
namespace ThomGame.Construction

open Analysis
open scoped BigOperators

variable {d : ℕ}

noncomputable def wheelLambdaAssignment
    (f : MatrixAssignment (SolutionGroup.Generator Col) d) : MatrixAssignment Lambda.Generator d :=
  FreeGroup.lift (InvolutionWords.generatorImage
    (fun s : Ordinary => f (FreeGroup.of (some (.inl s)))))

theorem wheel_size_le_total (r : WheelIndex) : wheelFamily.size r ≤ 472384 := by
  rw [← total_length]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)

theorem wheelLambda_source_bound {δ : ℝ} (hδ : 0 ≤ δ)
    (f : MatrixAssignment (SolutionGroup.Generator Col) d)
    (hf : IsApproxRepresentation (SolutionGroup.relators system) δ f) (r : WheelIndex) :
    unitaryDist (wheelLambdaAssignment f (FreeGroup.mk (sourceWord r)))
      (if wheelFamily.parity r = 1 then f (FreeGroup.of none) else 1) ≤
        (wheelFamily.size r * 15 : ℕ) * δ := by
  let u : Ordinary → UnitaryMatrix d := fun s => f (FreeGroup.of (some (.inl s)))
  have hs (s : Ordinary) : unitaryLength (u s * u s) ≤ δ := by
    simpa only [map_mul, Nat.cast_one, one_mul, u] using
      (solution_square_area system (.inl s)).unitaryLength_le f δ hf
  have hsub := InvolutionWords.substitute_product_error u hδ hs (sourceWord r)
  have hwh := wheelFamily.approximate_word_product f hf r
  have hprod : (List.ofFn (fun j => f (FreeGroup.of (some (.inl (wheelFamily.letter r j)))))).prod =
      ((wheelWord r).map u).prod := by
    change (List.ofFn (fun j : Fin (wheelWord r).length => u ((wheelWord r)[j.val]))).prod = _
    rw [List.ofFn_getElem_eq_map]
  rw [hprod] at hwh
  change unitaryDist ((wheelWord r).map u).prod
    (wheelLambdaAssignment f (FreeGroup.mk (sourceWord r))) ≤ _ at hsub
  rw [← wheel_size_eq r] at hsub
  have ht := unitaryDist_triangle (wheelLambdaAssignment f (FreeGroup.mk (sourceWord r)))
    ((wheelWord r).map u).prod
    (if wheelFamily.parity r = 1 then f (FreeGroup.of none) else 1)
  rw [unitaryDist_comm _ ((wheelWord r).map u).prod] at ht
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hwh ⊢
  linarith

theorem wheelLambda_J_bound {δ : ℝ} (hδ : 0 ≤ δ)
    (f : MatrixAssignment (SolutionGroup.Generator Col) d)
    (hf : IsApproxRepresentation (SolutionGroup.relators system) δ f) :
    unitaryDist (wheelLambdaAssignment f (FreeGroup.of (72 : Lambda.Generator)))
      (f (FreeGroup.of none)) ≤ 60 * δ := by
  have h := wheelLambda_source_bound hδ f hf none
  change unitaryDist (wheelLambdaAssignment f (FreeGroup.of (72 : Lambda.Generator)))
    (f (FreeGroup.of none)) ≤ ((4 * 15 : ℕ) : ℝ) * δ at h
  norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at h
  exact h

theorem wheelLambda_normalized_bound {δ : ℝ} (hδ : 0 ≤ δ)
    (f : MatrixAssignment (SolutionGroup.Generator Col) d)
    (hf : IsApproxRepresentation (SolutionGroup.relators system) δ f)
    (w : Word Lambda.Generator) (hw : w ∈ Lambda.normalizedRelators) :
    unitaryLength (wheelLambdaAssignment f (FreeGroup.mk w)) ≤ 7085760 * δ := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hw
  have hb := wheelLambda_source_bound hδ f hf (some i)
  have hsize : (wheelFamily.size (some i) * 15 : ℕ) ≤ 7085760 := by
    have := wheel_size_le_total (some i)
    omega
  have hcoeff : ((wheelFamily.size (some i) * 15 : ℕ) : ℝ) * δ ≤ 7085760 * δ :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hsize) hδ
  have he : sourceWord (some i) = w := hi
  simpa only [he, wheelFamily, zero_ne_one, ite_false, unitaryLength] using hb.trans hcoeff

theorem wheelLambda_isApprox_raw {δ : ℝ} (hδ : 0 ≤ δ)
    (f : MatrixAssignment (SolutionGroup.Generator Col) d)
    (hf : IsApproxRepresentation (SolutionGroup.relators system) δ f) :
    IsApproxRepresentation Lambda.rawRelationSet (7085760 * δ) (wheelLambdaAssignment f) := by
  rintro _ ⟨w, hw, rfl⟩
  rw [← assignment_word_eval, ← unitaryLength_eval_canonical]
  by_cases he : Lambda.canonical w = []
  · simp only [he, Word.eval_nil, unitaryLength_one]
    positivity
  · rw [assignment_word_eval]
    exact wheelLambda_normalized_bound hδ f hf _
      ((Lambda.mem_normalizedRelators _).mpr ⟨w, hw, rfl, he⟩)

noncomputable def paperToWheelAssignment
    (f : MatrixAssignment (SolutionGroup.Generator (Fin 1889684)) d) :
    MatrixAssignment (SolutionGroup.Generator Col) d := reindexedMatrixAssignment colEquiv f

theorem paperToWheel_isApprox {δ : ℝ}
    (f : MatrixAssignment (SolutionGroup.Generator (Fin 1889684)) d)
    (hf : IsApproxRepresentation (SolutionGroup.Paper.relators paperSystem) δ f) :
    IsApproxRepresentation (SolutionGroup.relators system) (4 * δ) (paperToWheelAssignment f) :=
  isApprox_reindexedMatrixAssignment system rowEquiv colEquiv f
    (paper_ordered_approx_to_original numberedSystem f hf)

/-- All raw Lambda relations, including the HNN relation, have this explicit defect. -/
theorem paperToLambda_isApprox {δ : ℝ} (hδ : 0 ≤ δ)
    (f : MatrixAssignment (SolutionGroup.Generator (Fin 1889684)) d)
    (hf : IsApproxRepresentation (SolutionGroup.Paper.relators paperSystem) δ f) :
    IsApproxRepresentation Lambda.rawRelationSet (28343040 * δ)
      (wheelLambdaAssignment (paperToWheelAssignment f)) := by
  convert wheelLambda_isApprox_raw (by positivity : 0 ≤ 4 * δ)
    (paperToWheelAssignment f) (paperToWheel_isApprox f hf) using 1 <;> ring

theorem paperToLambda_J_bound {δ : ℝ} (hδ : 0 ≤ δ)
    (f : MatrixAssignment (SolutionGroup.Generator (Fin 1889684)) d)
    (hf : IsApproxRepresentation (SolutionGroup.Paper.relators paperSystem) δ f) :
    unitaryDist (wheelLambdaAssignment (paperToWheelAssignment f)
      (FreeGroup.of (72 : Lambda.Generator))) (f (FreeGroup.of none)) ≤ 240 * δ := by
  have h := wheelLambda_J_bound (by positivity : 0 ≤ 4 * δ)
    (paperToWheelAssignment f) (paperToWheel_isApprox f hf)
  simpa only [paperToWheelAssignment, reindexedMatrixAssignment_of, Option.map_none,
    show (60 : ℝ) * (4 * δ) = 240 * δ by ring] using h

end ThomGame.Construction
