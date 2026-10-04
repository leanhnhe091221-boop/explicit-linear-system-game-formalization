module

public import ThomGame.Groups.CompressorGroup
public import ThomGame.Finite.WordSubgroup
public import Mathlib.Algebra.Group.Subgroup.Map

/-!
# The positive shears compress the actual subgroup H

This proof uses the specified action relations and their positive target
words. It proves inclusion; strictness needs the separate Laurent model.
-/

@[expose] public section
namespace ThomGame.Compressor

def shearElement (s : Root) : GroupQ := ofGenerator (.inr s)

theorem mem_roots : ∀ r : Root, r ∈ roots := by decide +kernel
theorem mem_coefficients : ∀ m : Coeff, m ∈ coefficients := by decide +kernel

theorem action_relator_mem (s r : Root) (ε : Bool) (m : Coeff) :
    Word.equation (conjugate (signed (shear s) ε) (X r m)) (actionTarget s r ε m) ∈ rawRelators := by
  have h : Word.equation (conjugate (signed (shear s) ε) (X r m)) (actionTarget s r ε m) ∈
      actionRelations := by
    unfold actionRelations
    apply List.mem_flatMap.mpr
    refine ⟨s, mem_roots s, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨ε, by cases ε <;> simp, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨r, mem_roots r, ?_⟩
    exact List.mem_map.mpr ⟨m, mem_coefficients m, rfl⟩
  simp only [rawRelators, List.mem_append]
  tauto

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem actionTarget_positive : ∀ s r m,
    positive (.inl (r, m)) = true →
      ∀ a ∈ actionTarget s r true m, positive a.1 = true := by decide +kernel

theorem positive_shear_action (s r : Root) (m : Coeff) :
    shearElement s * ofGenerator (.inl (r, m)) * (shearElement s)⁻¹ =
      Word.eval ofGenerator (actionTarget s r true m) := by
  have h := eval_rawRelator _ (action_relator_mem s r true m)
  rw [Word.eval_equation_eq_one_iff] at h
  simpa [conjugate, signed, shear, X, shearElement, mul_assoc] using h

theorem shear_positive_generator (s : Root) (g : Generator) (hg : positive g = true) :
    shearElement s * ofGenerator g * (shearElement s)⁻¹ ∈ positiveSubgroup := by
  cases g with
  | inl p =>
    rcases p with ⟨r, m⟩
    rw [positive_shear_action]
    apply Word.eval_mem
    intro a ha
    exact ofGenerator_mem_positiveSubgroup a.1 (actionTarget_positive s r m hg a ha)
  | inr r => simp [positive] at hg

theorem shear_compresses (s : Root) (x : GroupQ) (hx : x ∈ positiveSubgroup) :
    shearElement s * x * (shearElement s)⁻¹ ∈ positiveSubgroup := by
  have hclosed : positiveSubgroup ≤
      positiveSubgroup.comap (MulAut.conj (shearElement s)).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨g, hg, rfl⟩
    exact shear_positive_generator s g hg
  exact hclosed hx

theorem shear_conjugate_subgroup_le (s : Root) :
    positiveSubgroup.map (MulAut.conj (shearElement s)).toMonoidHom ≤ positiveSubgroup := by
  rintro _ ⟨x, hx, rfl⟩
  exact shear_compresses s x hx

theorem t_conjugate_subgroup_le :
    positiveSubgroup.map (MulAut.conj tElement).toMonoidHom ≤ positiveSubgroup :=
  shear_conjugate_subgroup_le root12

theorem backwardConjugate_mem_iff :
    backwardConjugate ∈ positiveSubgroup ↔
      hElement ∈ positiveSubgroup.map (MulAut.conj tElement).toMonoidHom := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  rfl

end ThomGame.Compressor
