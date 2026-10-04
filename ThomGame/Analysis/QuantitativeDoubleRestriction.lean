module

public import ThomGame.Analysis.SolutionRowApproximation
public import ThomGame.Groups.DoubleToLambda

/-! Restrict a raw Lambda matrix assignment to the actual 72 double generators. -/

@[expose] public section
namespace ThomGame.Analysis

variable {d : ℕ}

noncomputable def lambdaDoubleAssignment (f : MatrixAssignment Lambda.Generator d) :
    MatrixAssignment Double.Generator d := f.comp (FreeGroup.map Double.lambdaGenerator)

@[simp] theorem lambdaDoubleAssignment_of (f : MatrixAssignment Lambda.Generator d)
    (g : Double.Generator) :
    lambdaDoubleAssignment f (FreeGroup.of g) = f (FreeGroup.of (Double.lambdaGenerator g)) := by
  simp [lambdaDoubleAssignment]

theorem lambdaDouble_copyWord (f : MatrixAssignment Lambda.Generator d)
    (b : Bool) (w : Word Compressor.Generator) :
    lambdaDoubleAssignment f (FreeGroup.mk (Double.copyWord b w)) =
      f (FreeGroup.mk (Lambda.copyWord b w)) := by
  simp only [← assignment_word_eval, Double.copyWord, Lambda.copyWord,
    Word.eval_map_generators, lambdaDoubleAssignment_of, Double.lambdaGenerator_copy]

theorem lambdaDouble_isApprox {δ : ℝ} (f : MatrixAssignment Lambda.Generator d)
    (hf : IsApproxRepresentation Lambda.rawRelationSet δ f) :
    IsApproxRepresentation Double.relators δ (lambdaDoubleAssignment f) := by
  rintro _ ⟨w, hw, rfl⟩
  simp only [Double.rawRelators, List.mem_append, List.mem_map] at hw
  rcases hw with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
  · rw [lambdaDouble_copyWord]
    exact hf _ ⟨_, Double.lambda_copyRelator_mem false r hr, rfl⟩
  · rw [lambdaDouble_copyWord]
    exact hf _ ⟨_, Double.lambda_copyRelator_mem true r hr, rfl⟩

theorem lambdaDouble_obstruction (f : MatrixAssignment Lambda.Generator d) :
    lambdaDoubleAssignment f (FreeGroup.mk Double.obstructionWord) =
      f (FreeGroup.mk Lambda.w) := by
  simp only [← assignment_word_eval, Double.obstructionWord, Lambda.w, Lambda.h,
    Lambda.t₂, Lambda.t₁, Word.eval_commutator, Word.eval_append, Word.eval_inverse,
    Word.eval_generator, lambdaDoubleAssignment_of]
  rfl

theorem lambda_hnn_defect {δ : ℝ} (f : MatrixAssignment Lambda.Generator d)
    (hf : IsApproxRepresentation Lambda.rawRelationSet δ f) :
    unitaryDist (f (FreeGroup.of (73 : Lambda.Generator)) * f (FreeGroup.mk Lambda.w) *
      (f (FreeGroup.of (73 : Lambda.Generator)))⁻¹)
      (f (FreeGroup.mk Lambda.w) * f (FreeGroup.of (72 : Lambda.Generator))) ≤ δ := by
  have h := hf _ ⟨_, Lambda.hnn_relation_mem, rfl⟩
  rw [← assignment_word_eval] at h
  simpa only [Word.equation, Word.eval_append, Word.eval_inverse, Lambda.z, Lambda.J,
    Word.eval_generator, assignment_word_eval, unitaryDist_eq_length] using h

end ThomGame.Analysis
