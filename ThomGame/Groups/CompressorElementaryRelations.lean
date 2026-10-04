module

public import ThomGame.Groups.PrimeFiveRankThreeCover
public import ThomGame.Groups.CompressorCompression

/-! The actual ordered Q relations satisfy every prime-five cover equation. -/

@[expose] public section
namespace ThomGame.Compressor

open PrimeFiveRankThreeCover (comm)

private theorem eval_of_cover_family (w : Word Generator)
    (hw : w ∈ e0 ++ e1 ++ e2e3 ++ e4) : Word.eval ofGenerator w = 1 := by
  apply eval_rawRelator
  simp only [List.mem_append] at hw
  simp only [rawRelators, List.mem_append]
  tauto

theorem elementary_e0 (r : Root) (m : Coeff) : ofGenerator (.inl (r, m)) ^ 5 = 1 := by
  have hmem : power (X r m) 5 ∈ e0 := by
    exact List.mem_flatMap.mpr ⟨r, mem_roots r, List.mem_map.mpr ⟨m, mem_coefficients m, rfl⟩⟩
  have h := eval_of_cover_family _ (by simp only [List.mem_append]; tauto)
  simpa [power, X, pow_succ, mul_assoc] using h

theorem elementary_e1 (r s : Root) (m n : Coeff) (hrs : separated r s) :
    comm (ofGenerator (.inl (r, m))) (ofGenerator (.inl (s, n))) = 1 := by
  have hmem : Word.commutator (X r m) (X s n) ∈ e1 := by
    apply List.mem_flatMap.mpr
    refine ⟨r, mem_roots r, List.mem_flatMap.mpr ⟨s, mem_roots s, ?_⟩⟩
    simp only [hrs, ↓reduceIte]
    exact List.mem_flatMap.mpr ⟨m, mem_coefficients m, List.mem_map.mpr ⟨n, mem_coefficients n, rfl⟩⟩
  have h := eval_of_cover_family _ (by simp only [List.mem_append]; tauto)
  simpa [X, PrimeFiveRankThreeCover.comm] using h

theorem elementary_e2 (r : Root) (m : Coeff) :
    comm (ofGenerator (.inl (r, m))) (ofGenerator (.inl (right r, none))) =
      ofGenerator (.inl (across r, m)) := by
  have hmem : Word.equation (Word.commutator (X r m) (X (right r) none)) (X (across r) m) ∈ e2e3 := by
    exact List.mem_flatMap.mpr ⟨r, mem_roots r,
      List.mem_flatMap.mpr ⟨m, mem_coefficients m, by simp⟩⟩
  have h := eval_of_cover_family _ (by simp only [List.mem_append]; tauto)
  rw [Word.eval_equation_eq_one_iff] at h
  simpa [X, PrimeFiveRankThreeCover.comm] using h

theorem elementary_e3 (r : Root) (m : Coeff) :
    comm (ofGenerator (.inl (r, none))) (ofGenerator (.inl (right r, m))) =
      ofGenerator (.inl (across r, m)) := by
  have hmem : Word.equation (Word.commutator (X r none) (X (right r) m)) (X (across r) m) ∈ e2e3 := by
    exact List.mem_flatMap.mpr ⟨r, mem_roots r,
      List.mem_flatMap.mpr ⟨m, mem_coefficients m, by simp⟩⟩
  have h := eval_of_cover_family _ (by simp only [List.mem_append]; tauto)
  rw [Word.eval_equation_eq_one_iff] at h
  simpa [X, PrimeFiveRankThreeCover.comm] using h

theorem elementary_e4 (r s : Root) (m n l : Coeff) (hrs : separated (across r) s) :
    comm (comm (ofGenerator (.inl (r, m))) (ofGenerator (.inl (right r, n))))
      (ofGenerator (.inl (s, l))) = 1 := by
  have hmem : Word.commutator (Word.commutator (X r m) (X (right r) n)) (X s l) ∈ e4 := by
    apply List.mem_flatMap.mpr
    refine ⟨r, mem_roots r, List.mem_flatMap.mpr ⟨s, mem_roots s, ?_⟩⟩
    simp only [hrs, ↓reduceIte]
    exact List.mem_flatMap.mpr ⟨m, mem_coefficients m,
      List.mem_flatMap.mpr ⟨n, mem_coefficients n, List.mem_map.mpr ⟨l, mem_coefficients l, rfl⟩⟩⟩
  have h := eval_of_cover_family _ (by simp only [List.mem_append]; tauto)
  simpa [X, PrimeFiveRankThreeCover.comm] using h

def coverModel {d : Nat} (σ : PrimeFiveRankThreeCover.Coefficient d → Coeff) (hσ : σ none = none) :
    PrimeFiveRankThreeCover.Model d GroupQ where
  x r m := ofGenerator (.inl (r, σ m))
  e0 r m := elementary_e0 r (σ m)
  e1 r s m n hrs := elementary_e1 r s (σ m) (σ n) hrs
  e2 r m := by simpa only [hσ] using elementary_e2 r (σ m)
  e3 r m := by simpa only [hσ] using elementary_e3 r (σ m)
  e4 r s m n l hrs := elementary_e4 r s (σ m) (σ n) (σ l) hrs

end ThomGame.Compressor
