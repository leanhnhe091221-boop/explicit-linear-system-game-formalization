module

public import ThomGame.Analysis.PrimeFivePairCollection

/-! A bounded-area, inverse-compatible section of the universal pair group. -/

@[expose] public section
namespace ThomGame.Analysis.PairCollectionRelations

open RelatorEquality FinitePrimeFivePair

variable {G : Type*} [Group G] {r : ℕ} {rels : Set G} {a b : Fin r → G}

def wordAssignment (a b : Fin r → G) : Alphabet r → G
  | (false,i) => a i
  | (true,i) => b i

theorem eval_canonical_normal (g : FinitePrimeFivePair r) :
    Word.eval (wordAssignment a b) (canonicalWord g) = normal a b g := by
  simp only [canonicalWord, Word.eval_append, eval_vectorWord]
  simp [normal, A, C, indices, blockProduct, aWord, bWord, cWord,
    Word.eval_commutator, wordAssignment, pairCommutator, mul_assoc]

variable (h : PairCollectionRelations rels a b)
include h

theorem normal_inv (hr : r ≤ 7) (g : FinitePrimeFivePair r) :
    RelatorEquality rels (normal a b g⁻¹) (normal a b g)⁻¹ 1000000000 := by
  have hh := (h.normal_mul hr g⁻¹ g).mul_right (normal a b g)⁻¹
  simpa only [inv_mul_cancel, h.normal_one, mul_assoc, mul_inv_cancel, mul_one, one_mul] using hh

theorem section_normal (hr : r ≤ 7) (g : FinitePrimeFivePair r) :
    RelatorEquality rels (Word.eval (wordAssignment a b) (sectionWord g))
      (normal a b g) 1000000000 := by
  unfold sectionWord
  split_ifs with hg ho
  · subst g
    exact (RelatorEquality.of_eq (by simp [h.normal_one])).mono (by decide)
  · exact (RelatorEquality.of_eq (eval_canonical_normal g)).mono (by decide)
  · rw [Word.eval_inverse, eval_canonical_normal]
    simpa only [inv_inv] using (h.normal_inv hr g).inv

theorem section_mul (hr : r ≤ 7) (g k : FinitePrimeFivePair r) :
    RelatorEquality rels
      (Word.eval (wordAssignment a b) (sectionWord g) * Word.eval (wordAssignment a b) (sectionWord k))
      (Word.eval (wordAssignment a b) (sectionWord (g * k))) 4000000000 := by
  exact (((h.section_normal hr g).mul (h.section_normal hr k)).trans
    (h.normal_mul hr g k)).trans (h.section_normal hr (g*k)).symm

end ThomGame.Analysis.PairCollectionRelations
