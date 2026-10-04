module

public import ThomGame.Construction.Wheel
public import ThomGame.Groups.LambdaChecks

/-! Concrete dimensions of the constructed sparse wheel system. -/

@[expose] public section
namespace ThomGame.Construction

open scoped BigOperators

theorem ordinary_card : Fintype.card Ordinary = 148 := by
  simp [Ordinary, InvolutionWords.Generator, Lambda.Generator, Fintype.card_prod]

theorem wheel_count : Fintype.card WheelIndex = 12864 := by
  simp only [WheelIndex, Fintype.card_option, Fintype.card_fin, Lambda.normalized_relator_count]

private def wheelLengthFromSource (n : Nat) : Nat := 4 + 4 * n

private theorem family_length_of_list (rs : List (Word Lambda.Generator))
    (F : Wheel.Family (Option (Fin rs.length)) Ordinary)
    (hzero : F.size none = 4)
    (hsome : ∀ i : Fin rs.length, F.size (some i) = 4 * (rs[i.val]'i.isLt).length) :
    F.totalLength = wheelLengthFromSource (rs.map List.length).sum := by
  unfold wheelLengthFromSource
  rw [Wheel.Family.totalLength, Fintype.sum_option, hzero]
  simp_rw [hsome]
  rw [← Finset.mul_sum]
  congr 2
  rw [← List.sum_ofFn]
  exact congrArg List.sum (List.ofFn_getElem_eq_map rs List.length)

theorem total_length : wheelFamily.totalLength = 472384 :=
  (family_length_of_list Lambda.normalizedRelators wheelFamily wheel_size_none wheel_size_some).trans
    (congrArg wheelLengthFromSource Lambda.normalized_relator_total_length)

private def tripleCount (n : Nat) : Nat := 3 * n
private def columnCount (n : Nat) : Nat := 148 + 4 * n

private theorem row_count_formula {R V : Type*} [Fintype R] (F : Wheel.Family R V) :
    Fintype.card F.Row = tripleCount F.totalLength := F.row_card

private theorem col_count_formula {R V : Type*} [Fintype R] [Fintype V]
    (F : Wheel.Family R V) (h : Fintype.card V = 148) :
    Fintype.card F.Col = columnCount F.totalLength := by
  rw [F.col_card, h]
  rfl

private theorem nonzero_count_formula {R C : Type*} [Fintype R] [Fintype C] [DecidableEq C]
    (S : SparseSystem R C) :
    Fintype.card {p : R × C // S.matrix p.1 p.2 ≠ 0} = tripleCount (Fintype.card R) :=
  S.nonzero_card

theorem row_count : Fintype.card Row = 1417152 :=
  (row_count_formula wheelFamily).trans (congrArg tripleCount total_length)

theorem col_count : Fintype.card Col = 1889684 :=
  (col_count_formula wheelFamily ordinary_card).trans (congrArg columnCount total_length)

theorem nonzero_count :
    Fintype.card {p : Row × Col // system.matrix p.1 p.2 ≠ 0} = 4251456 :=
  (nonzero_count_formula system).trans (congrArg tripleCount row_count)

def oddRow : Row := ⟨none, 0, 0⟩

theorem rhs_ne_zero_iff (r : Row) : system.rhs r ≠ 0 ↔ r = oddRow := by
  rcases r with ⟨r, j, k⟩
  cases r with
  | none =>
    fin_cases j <;> fin_cases k <;> decide +kernel
  | some i =>
    constructor
    · intro h
      have hz : system.rhs ⟨some i, j, k⟩ = 0 := by
        change (if j = 0 ∧ k = 0 then (0 : ZMod 2) else 0) = 0
        exact ite_self _
      exact False.elim (h hz)
    · intro h
      have hi : (some i : WheelIndex) = none := congrArg Sigma.fst h
      cases hi

/-- Positions preceding a wheel, computed from an arbitrary source list. -/
def indexedOffset (rs : List (Word Lambda.Generator)) : Option (Fin rs.length) → Nat
  | none => (rs.map (fun w => (InvolutionWords.substitute w).length)).sum
  | some i => ((rs.take i.val).map (fun w => (InvolutionWords.substitute w).length)).sum

/-- The number of positions before the indicated wheel. -/
def offset : WheelIndex → Nat := indexedOffset Lambda.normalizedRelators

def indexedRowNumber (rs : List (Word Lambda.Generator))
    (r : Option (Fin rs.length)) (j k : Nat) : Nat := 3 * (indexedOffset rs r + j) + k + 1

/-- The one-based row formula used by the source matrix generator. -/
def rowNumber (r : Row) : Nat :=
  indexedRowNumber Lambda.normalizedRelators r.1 r.2.1.val r.2.2.val

private def oddNumberFromSource (n : Nat) : Nat := 3 * (4 * n) + 1

private theorem odd_number_formula (rs : List (Word Lambda.Generator)) :
    indexedRowNumber rs none 0 0 = oddNumberFromSource (rs.map List.length).sum := by
  simp [indexedRowNumber, indexedOffset, InvolutionWords.substitute_length,
    List.sum_map_mul_left, oddNumberFromSource]

theorem odd_row_number : rowNumber oddRow = 1417141 :=
  (odd_number_formula Lambda.normalizedRelators).trans
    (congrArg oddNumberFromSource Lambda.normalized_relator_total_length)

theorem rhs_nonzero_row_number (r : Row) (h : system.rhs r ≠ 0) :
    rowNumber r = 1417141 := by
  rw [(rhs_ne_zero_iff r).mp h]
  exact odd_row_number

end ThomGame.Construction
