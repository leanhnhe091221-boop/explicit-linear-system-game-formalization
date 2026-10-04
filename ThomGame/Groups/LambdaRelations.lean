module

public import ThomGame.Groups.LambdaPresentation
public import ThomGame.Finite.PresentedWords
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# The central element and HNN relation in the actual Λ presentation

These consequences use the explicitly generated raw relators. They do not
assert the base embedding or nontriviality of the central involution.
-/

@[expose] public section
namespace ThomGame.Lambda

def ofGenerator (g : Generator) : GroupLambda := PresentedGroup.of g

def JElement : GroupLambda := ofGenerator 72

def stableElement : GroupLambda := ofGenerator 73

def obstructionElement : GroupLambda := Word.eval ofGenerator w

theorem eval_rawRelator (r : Word Generator) (hr : r ∈ rawRelators) :
    Word.eval ofGenerator r = 1 := by
  change Word.eval (PresentedGroup.of (rels := rawRelationSet)) r = 1
  rw [Word.eval_presented]
  exact PresentedGroup.one_of_mem ⟨r, hr, rfl⟩

theorem J_square_mem : J ++ J ∈ rawRelators := by
  simp only [rawRelators, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    true_or, or_true]

theorem J_z_commutator_mem : Word.commutator J z ∈ rawRelators := by
  simp only [rawRelators, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    true_or, or_true]

theorem hnn_relation_mem : Word.equation (z ++ w ++ Word.inverse z) (w ++ J) ∈ rawRelators := by
  simp only [rawRelators, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    or_true]

theorem mem_amalgamGenerators (g : Generator) (hg : g.val < 72) : g ∈ amalgamGenerators := by
  apply List.mem_map.mpr
  refine ⟨⟨g.val, hg⟩, List.mem_finRange _, ?_⟩
  exact Fin.ext rfl

theorem J_amalgam_commutator_mem (g : Generator) (hg : g.val < 72) :
    Word.commutator J (Word.generator g) ∈ rawRelators := by
  have h : Word.commutator J (Word.generator g) ∈
      amalgamGenerators.map (fun a => Word.commutator J (Word.generator a)) :=
    List.mem_map.mpr ⟨g, mem_amalgamGenerators g hg, rfl⟩
  simp only [rawRelators, List.mem_append]
  exact Or.inl (Or.inr h)

theorem JElement_square : JElement * JElement = 1 := by
  simpa [J, JElement] using eval_rawRelator (J ++ J) J_square_mem

theorem JElement_commutes_generator (g : Generator) : Commute JElement (ofGenerator g) := by
  by_cases hg : g = 72
  · subst g
    exact Commute.refl _
  have hmem : Word.commutator J (Word.generator g) ∈ rawRelators := by
    by_cases hz : g = 73
    · subst g
      exact J_z_commutator_mem
    · apply J_amalgam_commutator_mem
      have hg' : g.val ≠ 72 := by intro he; exact hg (Fin.ext he)
      have hz' : g.val ≠ 73 := by intro he; exact hz (Fin.ext he)
      omega
  have h := eval_rawRelator _ hmem
  rw [Word.eval_commutator, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
  change JElement * ofGenerator g = ofGenerator g * JElement
  simpa [J, JElement] using h

private theorem presented_central {S : Type*} (rs : Set (FreeGroup S))
    (j : PresentedGroup rs) (hj : ∀ a : S, Commute j (PresentedGroup.of a))
    (g : PresentedGroup rs) : Commute j g := by
  have hgen : ∀ a : S, PresentedGroup.of (rels := rs) a ∈
      Subgroup.centralizer ({j} : Set (PresentedGroup rs)) := by
    intro a
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hj a).eq.symm
  have h := PresentedGroup.generated_by rs
    (Subgroup.centralizer ({j} : Set (PresentedGroup rs))) hgen g
  exact (Subgroup.mem_centralizer_singleton_iff.mp h).symm

theorem JElement_central (g : GroupLambda) : Commute JElement g :=
  presented_central rawRelationSet (PresentedGroup.of 72) JElement_commutes_generator g

theorem stable_conjugates_obstruction :
    stableElement * obstructionElement * stableElement⁻¹ = obstructionElement * JElement := by
  have h := eval_rawRelator _ hnn_relation_mem
  rw [Word.eval_equation_eq_one_iff] at h
  simpa [Word.eval_append, Word.eval_inverse, z, J, stableElement, obstructionElement, JElement,
    mul_assoc]
    using h

/-- For an actual homomorphism, the HNN relation transfers triviality of w
to triviality of J. Establishing that all relevant homomorphisms kill w is
the separate analytic part of the paper. -/
theorem hom_J_eq_one_of_obstruction_eq_one {G : Type*} [Group G]
    (φ : GroupLambda →* G) (hw : φ obstructionElement = 1) : φ JElement = 1 := by
  have h := congrArg φ stable_conjugates_obstruction
  simpa [hw] using h.symm

end ThomGame.Lambda
