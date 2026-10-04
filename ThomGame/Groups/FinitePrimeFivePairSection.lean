module

public import ThomGame.Groups.FinitePrimeFivePairWords

/-! An inverse-compatible section of the finite pair group, retaining the same
uniform expanded word-length bound. -/

@[expose] public section
namespace ThomGame.FinitePrimeFivePair

variable {r : ℕ}

noncomputable def sectionIndex (g : FinitePrimeFivePair r) :
    Fin (Fintype.card (FinitePrimeFivePair r)) := Fintype.equivFin _ g

noncomputable def sectionWord (g : FinitePrimeFivePair r) : Word (Alphabet r) :=
  if g = 1 then [] else
    if sectionIndex g < sectionIndex g⁻¹ then canonicalWord g else Word.inverse (canonicalWord g⁻¹)

@[simp] theorem sectionWord_one : sectionWord (1 : FinitePrimeFivePair r) = [] := by
  simp [sectionWord]

theorem eval_sectionWord (g : FinitePrimeFivePair r) : Word.eval generator (sectionWord g) = g := by
  unfold sectionWord
  split_ifs with h h'
  · simp [h]
  · exact eval_canonicalWord g
  · rw [Word.eval_inverse, eval_canonicalWord, inv_inv]

theorem sectionWord_length (g : FinitePrimeFivePair r) :
    (sectionWord g).length ≤ 8 * r + 16 * r ^ 2 := by
  unfold sectionWord
  split_ifs
  · simp
  · exact canonicalWord_length g
  · simpa only [Word.inverse, FreeGroup.invRev_length] using canonicalWord_length g⁻¹

theorem sectionWord_length_le_840 (hr : r ≤ 7) (g : FinitePrimeFivePair r) :
    (sectionWord g).length ≤ 840 := by
  have h := sectionWord_length g
  nlinarith

theorem sectionWord_inv (g : FinitePrimeFivePair r) :
    sectionWord g⁻¹ = Word.inverse (sectionWord g) := by
  by_cases h : g = 1
  · simp [h, Word.inverse]
  have hi : g⁻¹ ≠ 1 := by
    intro he
    apply h
    calc g = (g⁻¹)⁻¹ := (inv_inv g).symm
         _ = 1 := by rw [he, inv_one]
  have hne : sectionIndex g ≠ sectionIndex g⁻¹ := by
    intro he
    have hg : g = g⁻¹ := (Fintype.equivFin _).injective he
    exact h (eq_one_of_eq_inv g hg)
  by_cases ho : sectionIndex g < sectionIndex g⁻¹
  · have hn : ¬ sectionIndex g⁻¹ < sectionIndex g := not_lt_of_ge ho.le
    simp only [sectionWord, h, hi, ite_false, inv_inv, ho, hn, ite_true]
  · have hn : sectionIndex g⁻¹ < sectionIndex g := lt_of_le_of_ne (le_of_not_gt ho) hne.symm
    simp only [sectionWord, h, hi, ite_false, inv_inv, ho, hn, ite_true,
      Word.inverse, FreeGroup.invRev_invRev]

end ThomGame.FinitePrimeFivePair
