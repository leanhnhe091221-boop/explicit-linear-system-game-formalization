module

public import ThomGame.Analysis.QuantitativeWheel

/-! Every wheel relation has an explicit derivation using fourteen defining
solution-group relators per word position. -/

@[expose] public section
namespace ThomGame.Analysis

theorem word_eval_freeGroup_of {A : Type*} (w : Word A) :
    Word.eval FreeGroup.of w = FreeGroup.mk w := FreeGroup.lift_of_apply _

variable {R C : Type*} (S : SparseSystem R C)

theorem solution_square_area (c : C) :
    RelatorArea (SolutionGroup.relators S)
      (FreeGroup.of (some c) * FreeGroup.of (some c)) 1 := by
  have h := RelatorArea.relator (rels := SolutionGroup.relators S)
    (show FreeGroup.mk (SolutionGroup.relatorWord S (.variableSquare c)) ∈
      SolutionGroup.relators S from ⟨.variableSquare c, rfl⟩)
  rw [← word_eval_freeGroup_of] at h
  simpa [SolutionGroup.relatorWord, SolutionGroup.variableWord] using h

theorem solution_commutator_area (r : R) (i j : Fin 3) :
    RelatorArea (SolutionGroup.relators S)
      ((FreeGroup.of (some (S.column r i)) * FreeGroup.of (some (S.column r j))) *
        (FreeGroup.of (some (S.column r j)) * FreeGroup.of (some (S.column r i)))⁻¹) 1 := by
  have h := RelatorArea.relator (rels := SolutionGroup.relators S)
    (show FreeGroup.mk (SolutionGroup.relatorWord S (.rowCommutes r i j)) ∈
      SolutionGroup.relators S from ⟨.rowCommutes r i j, rfl⟩)
  rw [← word_eval_freeGroup_of] at h
  simpa [SolutionGroup.relatorWord, SolutionGroup.variableWord, mul_inv_rev, mul_assoc] using h

theorem solution_row_area (r : R) :
    RelatorArea (SolutionGroup.relators S)
      ((FreeGroup.of (some (S.column r 0)) * FreeGroup.of (some (S.column r 1)) *
        FreeGroup.of (some (S.column r 2))) *
          (if S.rhs r = 1 then FreeGroup.of none else 1)⁻¹) 1 := by
  have h := RelatorArea.relator (rels := SolutionGroup.relators S)
    (show FreeGroup.mk (SolutionGroup.relatorWord S (.rowEquation r)) ∈
      SolutionGroup.relators S from ⟨.rowEquation r, rfl⟩)
  rw [← word_eval_freeGroup_of] at h
  by_cases hr : S.rhs r = 1 <;>
    simpa [SolutionGroup.relatorWord, Word.equation, SolutionGroup.rowWord,
      SolutionGroup.rhsWord, SolutionGroup.variableWord, SolutionGroup.centralWord,
      hr, mul_assoc] using h

end ThomGame.Analysis

namespace ThomGame.Wheel.Family

open Analysis

variable {R V : Type*} (F : Family R V)

theorem solution_word_area (r : R) :
    RelatorArea (SolutionGroup.relators F.system)
      ((List.ofFn (fun j => FreeGroup.of (some (.inl (F.letter r j)) :
        SolutionGroup.Generator F.Col))).prod *
        (if F.parity r = 1 then FreeGroup.of none else 1)⁻¹) (F.size r * 14) := by
  apply RelatorArea.wheel_word_area _
    (fun j => FreeGroup.of (some (F.aux r j 0)))
    (fun j => FreeGroup.of (some (F.aux r j 1)))
    (fun j => FreeGroup.of (some (F.aux r j 2)))
    (fun j => FreeGroup.of (some (F.aux r j 3))) _
  · intro j; exact solution_square_area F.system _
  · intro j; exact solution_square_area F.system _
  · intro j; exact solution_square_area F.system _
  · intro j; exact solution_square_area F.system _
  · intro j
    have h := solution_row_area F.system ⟨r, j, 0⟩
    by_cases hj : j = 0 <;> simpa [system, columns, hj] using h
  · intro j
    have h := solution_row_area F.system ⟨r, j, 1⟩
    simpa [system, columns] using h
  · intro j
    have h := solution_row_area F.system ⟨r, j, 2⟩
    simpa [system, columns] using h
  · intro j
    exact solution_commutator_area F.system ⟨r, j, 0⟩ 1 2
  · intro j
    exact solution_commutator_area F.system ⟨r, j, 1⟩ 1 2
  · intro j
    exact solution_commutator_area F.system ⟨r, j, 2⟩ 1 2

theorem approximate_word_product {d : ℕ} {δ : ℝ}
    (f : MatrixAssignment (SolutionGroup.Generator F.Col) d)
    (hf : IsApproxRepresentation (SolutionGroup.relators F.system) δ f) (r : R) :
    unitaryDist (List.ofFn (fun j => f (FreeGroup.of (some (.inl (F.letter r j)))))).prod
      (if F.parity r = 1 then f (FreeGroup.of none) else 1) ≤ (F.size r * 14 : ℕ) * δ := by
  have h := (F.solution_word_area r).unitaryDist_le f δ hf
  simpa only [map_list_prod, List.map_ofFn, Function.comp_def, apply_ite, map_one] using h

end ThomGame.Wheel.Family
