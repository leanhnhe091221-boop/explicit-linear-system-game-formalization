module

public import ThomGame.Construction.Counts
public import ThomGame.Finite.WheelNumbering
public import ThomGame.Finite.Reindex

/-!
# Exact row and column numberings

The first 148 columns are the ordinary involutions. Every word position then
contributes four auxiliary columns and three rows. The final odd wheel comes
after every ordinary wheel. Both encodings are bijections, not only injections
or cardinality comparisons.
-/

@[expose] public section
namespace ThomGame.Construction

open scoped BigOperators

private theorem prefix_formula (rs : List (Word Lambda.Generator))
    (F : Wheel.Family (Option (Fin rs.length)) Ordinary)
    (hs : ∀ i : Fin rs.length, F.size (some i) =
      (InvolutionWords.substitute (rs[i.val]'i.isLt)).length)
    (r : Option (Fin rs.length)) :
    BlockNumbering.prefixSum F.size r = indexedOffset rs r := by
  cases r with
  | none =>
    simp only [BlockNumbering.prefixSum, indexedOffset, hs]
    rw [← List.sum_ofFn]
    exact congrArg List.sum (List.ofFn_getElem_eq_map rs
      (fun w => (InvolutionWords.substitute w).length))
  | some i =>
    simp only [BlockNumbering.prefixSum, indexedOffset, hs]
    exact BlockNumbering.sum_get_take rs
      (fun w => (InvolutionWords.substitute w).length) i.val i.isLt.le

theorem prefix_eq_offset (r : WheelIndex) :
    BlockNumbering.prefixSum wheelFamily.size r = offset r :=
  prefix_formula Lambda.normalizedRelators wheelFamily wheel_size_some_substitute r

/-- The source's row order, now as a bijection to exactly the stated range. -/
def rowEquiv : Row ≃ Fin 1417152 := wheelFamily.slotNumbering 472384 3 total_length

/-- The order of the four auxiliary variables at each position. -/
def auxiliaryEquiv : wheelFamily.Auxiliary ≃ Fin 1889536 :=
  wheelFamily.slotNumbering 472384 4 total_length

theorem rowEquiv_number (r : Row) : (rowEquiv r).val + 1 = rowNumber r := by
  rcases r with ⟨r, j, k⟩
  change (wheelFamily.slotNumbering 472384 3 total_length ⟨r, j, k⟩).val + 1 = _
  rw [Wheel.Family.slotNumbering_val, prefix_eq_offset]
  rfl

theorem auxiliaryEquiv_val (r : WheelIndex) (j : Fin (wheelFamily.size r)) (k : Fin 4) :
    (auxiliaryEquiv ⟨r, j, k⟩).val = 4 * (offset r + j.val) + k.val := by
  change (wheelFamily.slotNumbering 472384 4 total_length ⟨r, j, k⟩).val = _
  rw [Wheel.Family.slotNumbering_val, prefix_eq_offset]

/-- False selects u, true selects v, in the order used in the source. -/
def ordinaryEquiv : Ordinary ≃ Fin 148 :=
  ((Equiv.refl (Fin 74)).prodCongr finTwoEquiv.symm).trans finProdFinEquiv

theorem ordinaryEquiv_number (g : Ordinary) :
    (ordinaryEquiv g).val + 1 = ordinaryNumber g := by
  rcases g with ⟨g, b⟩
  cases b <;> simp [ordinaryEquiv, ordinaryNumber, finTwoEquiv, finProdFinEquiv]
  all_goals omega

/-- Ordinary columns followed by all auxiliary columns, in exactly that order. -/
def colEquiv : Col ≃ Fin 1889684 :=
  (ordinaryEquiv.sumCongr auxiliaryEquiv).trans finSumFinEquiv

/-- The source's one-based column formula. -/
def colNumber : Col → Nat
  | .inl g => ordinaryNumber g
  | .inr ⟨r, j, k⟩ => 148 + 4 * (offset r + j.val) + k.val + 1

theorem colEquiv_number (c : Col) : (colEquiv c).val + 1 = colNumber c := by
  cases c with
  | inl g =>
    change (ordinaryEquiv g).val + 1 = ordinaryNumber g
    exact ordinaryEquiv_number g
  | inr p =>
    rcases p with ⟨r, j, k⟩
    change (148 + (auxiliaryEquiv ⟨r, j, k⟩).val) + 1 = _
    rw [auxiliaryEquiv_val]
    simp only [colNumber]
    omega

theorem rowNumber_injective : Function.Injective rowNumber := by
  intro a b hab
  apply rowEquiv.injective
  apply Fin.ext
  have h := hab
  rw [← rowEquiv_number, ← rowEquiv_number] at h
  omega

theorem colNumber_injective : Function.Injective colNumber := by
  intro a b hab
  apply colEquiv.injective
  apply Fin.ext
  have h := hab
  rw [← colEquiv_number, ← colEquiv_number] at h
  omega

/-- The concrete binary system with exactly the advertised numerical types. -/
def numberedSystem : SparseSystem (Fin 1417152) (Fin 1889684) :=
  system.reindex rowEquiv colEquiv

theorem numbered_column (r : Row) (i : Fin 3) :
    (numberedSystem.column (rowEquiv r) i).val + 1 = colNumber (system.column r i) := by
  rw [numberedSystem, system.reindex_column]
  exact colEquiv_number _

theorem numbered_rhs (r : Row) : numberedSystem.rhs (rowEquiv r) = system.rhs r :=
  system.reindex_rhs rowEquiv colEquiv r

theorem numbered_matrix (r : Row) (c : Col) :
    numberedSystem.matrix (rowEquiv r) (colEquiv c) = system.matrix r c :=
  system.reindex_matrix rowEquiv colEquiv r c

theorem numbered_no_solution : ¬ ∃ x, numberedSystem.Satisfies x :=
  system.reindex_no_solution rowEquiv colEquiv no_solution

theorem numbered_no_perfect_deterministic :
    ¬ ∃ alice bob, numberedSystem.PerfectDeterministic alice bob := by
  rw [numberedSystem.exists_perfect_iff_exists_solution]
  exact numbered_no_solution

theorem numbered_rhs_ne_zero_iff (r : Fin 1417152) :
    numberedSystem.rhs r ≠ 0 ↔ r.val + 1 = 1417141 := by
  obtain ⟨s, rfl⟩ := rowEquiv.surjective r
  rw [numbered_rhs, rhs_ne_zero_iff, rowEquiv_number]
  constructor
  · rintro rfl
    exact odd_row_number
  · intro h
    apply rowNumber_injective
    exact h.trans odd_row_number.symm

end ThomGame.Construction
